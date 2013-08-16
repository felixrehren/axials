
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
	InstallMethod( PrintString,
	[IsAttrVector],
	function( v )
		return Concatenation(PrintString(v!.v)," with attributes");
	end
);

InstallMethod( Axis,
	[IsAlg,IsVector,IsFusion],
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
	[IsAlg,IsVector,IsFusion,IsMultiplicativeElementWithInverse,IsFunction],
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
		return function(x) local d;
			d :=AxisHelper@.splitVector(a,x,Fields(Fusion(a)));
			return Sum([1..Length(d)],i->fs[i]*d[i]);
			end;
		end
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
	,	eigenvectorsMultStabSubsp := function( A, a, Uinf )
			local time, vv;
			time := Runtime();
			if not IsTrivial(Uinf)
			then vv := List(
				Eigenvectors(Rationals,List(Basis(Uinf),b->
					Coefficients(Basis(Uinf),Mult(A)(a,b)) )),
				v -> LinearCombination(Basis(Uinf),v) );
			else vv := [];
			fi;
			InfoPro("extract eigenvectors",time);
			return vv;
			end
	, eigspByMult := function( a )
			local vv;
			vv := AxisHelper@.eigenvectorsMultStabSubsp(Alg(a),Vector(a),
				AxisHelper@.maxmlMultStabSubsp(Alg(a),Vector(a),Alg(a)));
			return List( Fields(Fusion(a)),function(f) local ww, V;
				ww := FilteredPositions(vv,v->Mult(Alg(a))(Vector(a),v)=f*v);
				V := Subspace(Closure(Alg(a)),vv{ww});
				vv := vv{Difference([1..Length(vv)],ww)};
				return V; end
			);
			end
	, solver := function( fields )
			local P, mat, solns;
			P := PolynomialRing(Rationals,
				List([1..Length(fields)],i->Indeterminate(Rationals,i)));
			mat := List([1..Length(fields)],
				i -> Concatenation( List(fields,f->f^(i-1)), [P.(i)] )
			) * One(P);
			mat := Independify(SemiEchelonMatDestructive(mat).vectors,
				[1..Length(fields)]);
			solns := List(mat,m->m[Length(fields)+1]);
			return xx -> List(solns,s->Value(s,IndeterminatesOfPolynomialRing(P),xx));
			end
	, splitVector := function( a, v, eigv )
			local vv, i, eigvmat;
			vv := [v];
			for i in [1..Length(eigv)-1] do
				if LastNonzeroPos(v) > Dimension(Alg(a)) then return fail; fi;
				v := Mult(Alg(a))(Vector(a),v);
				if v = fail then return fail; fi;
				Add(vv,v);
			od;
			return AxisHelper@.solver(eigv)(vv);
			end
	, splitSpace := function( a, V, eigv )
			local rr, v, r;
			rr := [];
			for v in Basis(V) do
				r := AxisHelper@.splitVector( a,v,eigv );
				if r <> fail then Add(rr,r); fi;
			od;
			return List( [1..Length(eigv)], i -> Subspace(V,List(rr,r->r[i])) );
			end
	, linEigSp := function( v )
			local B, vimage, vv, ff, eigspBySplit, eigspByMult;
			if HasMiyamoto(v) then
				B := Basis(Closure(Alg(v)));
				vimage := List(B,b->Miyamoto(v)(b));
				vv := [
					Subspace(Closure(Alg(v)),List([1..Length(B)],i->B[i] + vimage[i])),
					Subspace(Closure(Alg(v)),List([1..Length(B)],i->B[i] - vimage[i]))
				];
				ff := [
					Filtered(Fields(Fusion(v)),f->not f in Miyamoto(Fusion(v))),
					Miyamoto(Fusion(v))
				];
				eigspBySplit := Concatenation(List([1,2],i->
					AxisHelper@.splitSpace( v, vv[i], ff[i] ) ));
			else
				eigspBySplit := AxisHelper@.splitSpace(v, Alg(v), Fields(Fusion(v)));
			fi;
			eigspByMult := AxisHelper@.eigspByMult(v);
			return List([1..Length(Fields(Fusion(v)))],
				i -> eigspBySplit[i] + eigspByMult[i]);
			end
	, fusionClose := function( a, eigSp )
			local fields, fminus, fplus, fuse, eigMBs, new, addev, u, v, f, xx, i;
			fields := Fields(Fusion(a));
			fminus := Set(Miyamoto(Fusion(a)));
			fplus  := Set(Difference(fields,fminus));
			fuse := Fuse(Fusion(a));

			eigMBs :=List(eigSp,sp -> MutableBasis(Rationals,Basis(sp),Zero(Closure(Alg(a)))));
			new := Concatenation(List([1..Length(fields)],i->
				List(Basis(eigSp[i]),b->[fields[i],b]) ));

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
			#		if f = fminus or f = fplus then continue; fi;		# not sure
					xx := AxisHelper@.splitVector(a,Mult(Alg(a))(u[2],v[2]),f);
					if xx = fail then continue; fi;
					for i in [1..Length(f)]
					do addev(f[i],xx[i]); od;
				od;
				Remove(new,1);
			od;

			return List(eigMBs,mb -> Subspace(Closure(Alg(a)),BasisVectors(mb)));
			end
	)
);

InstallMethod( IsIdempotent,
	[IsAttrVector and HasAlg],
	v -> Mult(Alg(v))(v,v) = v
	);
InstallMethod( Eigenspaces,
	[IsAxis],
	function(v)
		if HasIsClosed(Alg(v)) and IsClosed(Alg(v))
		then return true;
		else return AxisHelper@.fusionClose(v,AxisHelper@.linEigSp(v));
		fi;
	end
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
	Error();
	S := Sum(II,I->Intersection(I[1],I[2]));
	if not IsTrivial(S)
	then AddRelations( Alg(a), S ); fi;
	InfoPro("directicity",time);
	return S;
	end
	);

