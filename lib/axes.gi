
#
#	axes implementation
#

InstallMethod( Axis,
	[IsMalg,IsVector,IsMtheory],
	function( A, v, th )
	SetMalg(v,A);
	SetMtheory(v,th);
	return v;
	end
	);
	InstallMethod( ViewString,
	[IsAxis],
	a -> "axis"
);

InstallValue( AxisHelper@,
	rec(
		maxmlMultStabSubsp := function( A, a, V )
			local time, U, i, Uinf, b, v, j, S;
			time := Runtime();
			U := [V];
			i := 1;
			while true do
				U[i+1] := ImageUnderMult( a, U[i] );
				if IsTrivial(U[i+1]) or (U[i] = U[i+1])
				then break; fi;
				i := i+1;
			od;
			Uinf := MutableBasis(Rationals, Basis(U[i]), Zero(A));
			for b in Basis(V) do
				v := ShallowCopy(b);
				for j in [1..i] do
					v := Mult(A)(a,v);
					if v = fail then break;
					elif v in U[i] then CloseMutableBasis(Uinf, b); break; fi;
				od;
			od;
			S := Subspace( A!.V, BasisVectors(Uinf) );
			InfoPro("mult-stable subspace",time);
			return S;
			end
	,	eigenvectorsMultStabSubsp := function( A, a, Uinf )
			local time, vv;
			time := Runtime();
			if not IsTrivial(Uinf)
			then vv := List(
				Eigenvectors(List(Basis(Uinf),b->
					Coefficients(Basis(Uinf),Mult(A)(a,b)) )),
				v -> LinearCombination(Basis(Uinf),v) );
			else vv := [];
			fi;
			InfoPro("extract eigenvectors",time);
			return vv;
			end
	)
);

InstallMethod( Idempotent,
	[IsVector and HasMalg],
	v -> Mult(Alg(v))(v,v) = v
	);
InstallMethod( Eigenvectors,
	[IsVector and HasMalg],
	v -> AxisHelper@.eigenvectorsMultStabSubsp(
		Malg(v),v,AxisHelper@.maxmlMultStabSubsp(Malg(v),v,Malg(v)!.V))
	);
InstallMethod( Eigenvectors,
	[IsVector and HasMalg and HasMiyamoto],
	v -> fail
	);
	


