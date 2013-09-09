
#
#	axes implementation
#

InstallMethod( Vector,
	[IsAttrVector],
	v -> v!.v
	);
	InstallMethod( \=,
	[IsAttrVector,IsAttrVector],
	function( u, v )
	return u!.v = v!.v;
	end
	);
	InstallMethod( \=,
	[IsAttrVector,IsVector],
	function( u, v )
	return u!.v = v;
	end
	);
	InstallMethod( \=,
	[IsAttrVector,IsVector],
	function( u, v )
	return u = v!.v;
	end
	);
	InstallMethod( \<,
	[IsAttrVector,IsAttrVector],
	function( u, v )
	return u!.v < v!.v;
	end
	);
	InstallMethod( \<,
	[IsAttrVector,IsVector],
	function( u, v )
	return u!.v < v;
	end
	);
	InstallMethod( \<,
	[IsAttrVector,IsVector],
	function( u, v )
	return u < v!.v;
	end
	);
	InstallMethod( PrintString,
	[IsAttrVector],
	function( v )
		return Concatenation(PrintString(v!.v)," with attributes");
	end
);

InstallMethod( Ad,
	[IsAttrVector and HasAlg],
	v -> Ad(Alg(v))(Vector(v))
);

InstallValue( AxisHelper@,
	rec(
		maxmlMultStabSubsp := function( A, a, V )
			local time, U, i, Uinf, b, vv, j, S;
			time := Runtime();
			U := [V];
			i := 1;
			while true do
				U[i+1] := ImageUnderMult( a, U[i], A );
				if IsTrivial(U[i+1]) or (U[i] = U[i+1])
				then break; fi;
				i := i+1;
			od;
			Uinf := ShallowCopy(Basis(U[i]));
			for b in Basis(V) do
				vv := [b];
				for j in [1..i] do
					Add(vv,Mult(A)(a,vv[j]));
					if vv[j+1] = fail or not vv[j+1] in A then break;
					elif vv[j+1] in U[i] then Append(Uinf,vv); break; fi;
				od;
			od;			# this does not capture all of Uinf
			Uinf := Subspace( A, Uinf );
			InfoPro("mult-stable subspace",time);
			return Uinf;
			end
	, sortEigSps := function( es, ev, ff )
			return List(ff,function(f) local i;
				i := Position(ev,f);
				if i = fail then return TrivialSubspace(es[1]);
				else return es[i]; fi; end );
			end
	, eigspByMult := function( a )
			local time, Uinf, Uint, sp;
			time := Runtime();
			Uinf := AxisHelper@.maxmlMultStabSubsp(Alg(a),Vector(a),Alg(a));
			Uint := List(Basis(Uinf),b->Coefficients(Basis(Uinf),Mult(Alg(a))(Vector(a),b)));
			sp := List(Eigenspaces(LeftActingDomain(Uinf),Uint),
				es -> Subspace(Closure(Alg(a)),
					List(Basis(es),b->LinearCombination(Basis(Uinf),b))));
			if HasFusion(a) then
				sp := AxisHelper@.sortEigSps(
					sp,
					Eigenvalues(LeftActingDomain(Uinf),Uint),
					Fields(Fusion(a))*One(LeftActingDomain(Alg(a)))
				);
			fi;
			InfoPro("multspace",time);
			return sp;
			end
	, solver := function( fields )
			local P, mat, solns;
			P := PolynomialRing(DefaultField(fields),
				List([1..Length(fields)],i->Indeterminate(DefaultField(fields),i)));
			mat := List([1..Length(fields)],
				i -> Concatenation( List(fields,f->f^(i-1)), [P.(i)] )
			) * One(P);
			mat := Independify(SemiEchelonMatDestructive(mat).vectors,
				[1..Length(fields)]);
			solns := List(mat,m->m[Length(fields)+1]);
			return xx->List(solns,s->Value(s,IndeterminatesOfPolynomialRing(P),xx+0));
			end 	### +0 changes the internal representation of the object,
						### which is necessary for the function to work. (bug?)
	, splitVector := function( a, v, eigv )
			local vv, i, eigvmat;
			vv := [v];
			for i in [1..Length(eigv)-1] do
				#if LastNonzeroPos(v) > Dimension(Alg(a)) then return fail; fi;
				if not v in Alg(a) then return fail; fi;
				v := Mult(Alg(a))(Vector(a),v);
				if v = fail then return fail; fi;
				Add(vv,v);
			od;
			return AxisHelper@.solver(eigv)(vv);
			end
	, splitSpace := function( a, V, eigv )
			local time, rr, v, r, es;
			time := Runtime();
			rr := [];
			for v in Basis(V) do
				r := AxisHelper@.splitVector( a,v,eigv );
				if r <> fail then Add(rr,r); fi;
			od;
			es := List( [1..Length(eigv)], i -> Subspace(V,List(rr,r->r[i])) );
			InfoPro("split space",time);
			return es;
			end
	, linEigSp := function( v )
			local time, B, vimage, vv, ff, eigspBySplit, eigspByMult;
			time := Runtime();
			if not IsEmpty(Miyamoto(Fusion(v))) then
				B := Basis(Closure(Alg(v)));
				vimage := List(B,b->Miyamoto(v)(b));
				vv := [
					Subspace(Closure(Alg(v)),List([1..Length(B)],i->B[i] + vimage[i])),
					Subspace(Closure(Alg(v)),List([1..Length(B)],i->B[i] - vimage[i]))
				];
				InfoPro("V+ & V-",time);
				ff := [
					Filtered(Fields(Fusion(v)),f->not f in Miyamoto(Fusion(v))),
					Miyamoto(Fusion(v))
				];
				eigspBySplit := Concatenation(List([1,2],i->
					AxisHelper@.splitSpace( v, vv[i], ff[i] ) ));
			else
				eigspBySplit := AxisHelper@.splitSpace(v,Closure(Alg(v)), Fields(Fusion(v)));
			fi;
			eigspByMult := AxisHelper@.eigspByMult(v);
			return List([1..Length(Fields(Fusion(v)))],
				i -> eigspBySplit[i] + eigspByMult[i]);
			end
	, fusionClose := function( a, eigSp )
			local time, fields, fminus, fplus, fuse, eigMBs, new, addev, u, v, f, xx, i;
			time := Runtime();
			fields := Fields(Fusion(a));
			fminus := Set(Miyamoto(Fusion(a)));
			fplus  := Set(Difference(fields,fminus));
			fuse := Fuse(Fusion(a));

			eigMBs :=List(eigSp,sp -> MutableBasis(LeftActingDomain(Alg(a)),Basis(sp),Zero(Closure(Alg(a)))));
			new := Concatenation(List([1..Length(fields)],i->
				List(Basis(Intersection(Alg(a),eigSp[i])),b->[fields[i],b]) ));

			addev := function(f,v)
				local p;
				p := Position(fields,f);
				v := SiftedVector(eigMBs[p],v);
				if not IsZero(v) then
					CloseMutableBasis(eigMBs[p],v);
					if LastNonzeroPos(v)<=Dimension(Alg(a))
					then Add(new,[f,v]); fi;
				fi;
			end;

			while not IsEmpty(new) do
				u := new[1];
				for v in new do
					f := fuse(u[1],v[1]);
					if f = fminus or f = fplus then continue; fi;
					xx := AxisHelper@.splitVector(a,Mult(Alg(a))(u[2],v[2]),f);
					if xx = fail then continue; fi;
					for i in [1..Length(f)]
					do addev(f[i],xx[i]); od;
				od;
				Remove(new,1);
			od;

			new := List(eigMBs,mb -> Subspace(Closure(Alg(a)),BasisVectors(mb)));
			InfoPro("fusion",time);
			return new;
			end
	)
);

InstallMethod( Axis,
	[IsAlg,IsGeneralizedRowVector,IsFusion],
	function( A, v, th )
	local a;
	a := Objectify(
		TypeAttrVector@,
		rec(
			v := v,
		)
	);
	SetAlg(a,A);
	SetFusion(a,th);
	SetIsIdempotent(a,true);
	return a;
	end
	);
	InstallMethod( Axis,
	[IsAlg,IsGeneralizedRowVector,IsFusion,IsMultiplicativeElementWithInverse,IsFunction],
	function( A, v, th, g, tau )
	local a;
	a := Axis(A,v,th);
	SetInvolution(a,g);
	SetMiyamoto(a,tau);
	return a;
	end
	);
	InstallMethod( ViewString,
	[IsAxis],
	a -> "axis"
	);
	InstallMethod( Miyamoto,
	[IsAxis],
	function(a)
		local fs;
		fs := List(Fields(Fusion(a)),function(f)
			if f in Miyamoto(Fusion(a)) then return -1;
			else return 1; fi; end);
		if IsEmpty(fs) then return BasisVectors(Basis(Alg(a))); fi;
		return List(Basis(Alg(a)),function(x) local d;
			d := AxisHelper@.splitVector(a,x,Fields(Fusion(a)));
			return Sum([1..Length(d)],i->fs[i]*d[i]);
			end
		);
		end
);

InstallMethod( IsIdempotent,
	[IsAttrVector and HasAlg],
	v -> Mult(Alg(v))(v,v) = v
	);
InstallMethod( Eigenspaces,
	[IsAttrVector and HasAlg and HasFusion],
	function(v)
		if HasIsClosed(Alg(v)) and IsClosed(Alg(v))
		then
			return AxisHelper@.sortEigSps(
				Eigenspaces(LeftActingDomain(Alg(v)),Ad(v)),
				Eigenvalues(LeftActingDomain(Alg(v)),Ad(v)),
				Fields(Fusion(v))*One(LeftActingDomain(Alg(v)))
			);
		else return AxisHelper@.fusionClose(v,AxisHelper@.linEigSp(v));
		fi;
	end
	);
	InstallMethod( Eigenspaces,
	[IsAttrVector and HasAlg],
	function(v)
		if HasIsClosed(Alg(v)) and IsClosed(Alg(v))
		then return Eigenspaces(LeftActingDomain(Alg(v)),Ad(v));
		else return AxisHelper@.eigspByMult(v);
		fi;
	end
);

InstallMethod( Relations,
	[IsAxis],
	a ->
	CheckLinearity(a) + CheckDirectity(a) ### not good!
	);
InstallMethod( CheckLinearity,
	[IsAxis],
	function(a)
	local time, rr, i, b, S;
	time := Runtime();
	rr := [];
	for i in [1..Length(Fields(Fusion(a)))] do
		for b in Filtered(Basis(Eigenspaces(a)[i]),
							b -> LastNonzeroPos(b)<=Dimension(Alg(a))) do
			Add(rr,Fields(Fusion(a))[i]*b - Mult(Alg(a))(Vector(a),b));
		od;
	od;
	S := Subspace( Closure(Alg(a)), rr );
	if not IsTrivial(S)
	then AddRelations( Alg(a), S ); fi;
	InfoPro("linearity",time);
	return S;
	end
	);
InstallMethod( CheckDirectity,
	[IsAxis],
	function( a )
	local time, th, composites, pp, II, p, I, i, c, S;
	time := Runtime();
	th := Fusion(a);
	composites := Filtered(
		PartitionBy(Cartesian(Fields(th),Fields(th)),ff->Fuse(th)(ff[1],ff[2])),
		p -> Length(p[1]) > 1
	);
	pp := PartitionsSet(Set(Fields(th)),2);
	II := [];
	for p in pp do
		I := [
		 Sum(p[1],x->Eigenspaces(a)[Position(Fields(th),x)]),
		 Sum(p[2],x->Eigenspaces(a)[Position(Fields(th),x)])
		];
		for i in [1,2] do
			for c in Filtered(composites,c->IsSubset(p[i],c[1])) do
				I[i] := I[i] + Sum(c[2],fg -> 
					ImageUnderMult( 
						Eigenspaces(a)[Position(Fields(th),fg[1])],
						Eigenspaces(a)[Position(Fields(th),fg[2])],
						Alg(a)
					)
				);
			od;
		od;
		Add(II,I);
	od;
	S := Sum(II,I->Intersection(I[1],I[2]));
	if not IsTrivial(S)
	then AddRelations( Alg(a), S ); fi;
	InfoPro("directicity",time);
	return S;
	end
	);
InstallMethod( Check1Dimnlity,
	[IsAxis],
	function( a )
	local time, B, lm, adv, rr;
	time := Runtime();
	B := Eigenspaces(a)[Position(Fields(Fusion(a)),1)];
	if Dimension(B) = 1 then return [TrivialSubspace(B)]; fi;
	lm := Indeterminate(LeftActingDomain(Alg(a)));
	# v := Basis(B)[1] + lm*Basis(B)[2]
	# any codimension-1 ideal will contain v for some value of lm
	# if adv has a 0-eigenvalue then v lies in an ideal
	adv := Ad(Alg(a),B)(Basis(B)[1]) + lm*Ad(Alg(a),B)(Basis(B)[2]);
	rr := List(RootsOfPolynomial(Determinant(adv)),r->
		Subspace(B,[Basis(B)[1] + r*Basis(B)[2]]));
	if IsZero(Determinant(Ad(Alg(a),B)(Basis(B)[2])))
	then Add(rr,Subspace(B,Basis(B){[2]})); fi;
	if not IsEmpty(rr) then
		#do what? ??
	fi;
	InfoPro("1dimnlity",time);
	return rr;
	end
);

InstallMethod( CentralCharge,
	[IsAttrVector and HasAlg],
	function( v )
		if FT(Alg(v)) = fail then return fail;
		else return 1/2*Form(Alg(v))(Vector(v),Vector(v)); fi;
	end
	);
InstallMethod( Explosion,
	[IsIdempotent],
	function( v )
		local adv, p, B, ff;
		if not IsClosed(Alg(v)) then return fail; fi;
		adv := Ad(v);
		p := Position(Eigenvalues(LeftActingDomain(Alg(v)),adv),One(LeftActingDomain(Alg(v))));
		if p = fail then return fail; fi;
		B := Eigenspaces(LeftActingDomain(Alg(v)),adv)[p];
		if Dimension(B) = 1 then return [v];
		else
			ff := Filtered(
			 AlgHelper@.annihSubsets(Idempotents(Alg(v),B),Mult(Alg(v))),
				S -> Sum(S) = Vector(v)
			);
			if not Length(ff) = 1 then Error("wat"); fi;
			return ff[1];
		fi;
	end
	);

