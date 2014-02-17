
#
#	utilities implementation
#

# shortcuts
	Alt := AlternatingGroup;
	Aut := AutomorphismGroup;
	Dih := DihedralGroup;
	Sym := SymmetricGroup;

# lists: positions
	InstallMethod( FilteredPositions,
		[IsList,IsFunction],
		function( list, boolFn )
		return Filtered([1..Length(list)],i->boolFn(list[i])); end);
	InstallMethod( FirstPosition,
		[IsList,IsFunction],
		function( list, boolFn )
		return First([1..Length(list)],i->boolFn(list[i])); end);
	InstallMethod( NonzeroPos,
		[IsList],
		v -> FilteredPositions(v,x->not IsZero(x))
		);
	InstallMethod( LastNonzeroPos,
		[IsList],
		function( v )
		local l, f;
		l := Length(v);
		f := First([l,l-1..1],i->not IsZero(v[i]));
		if f = fail then return 0;
		else return f; fi;
		end);
	InstallMethod( KroneckerVector,
		[IsPosInt,IsPosInt],
		function(m,n)
		local v;
		v := [1..n]*0;
		v[m] := 1;
		return v;
		end);
	InstallMethod( Independify,
		[IsList,IsList],
		function( mat, pos )
			local i, j;
			for i in [1..Length(mat)] do
				mat[i] := mat[i]/mat[i][pos[i]];
				for j in [1..i-1]
				do mat[j] := mat[j] - mat[j][pos[i]]*mat[i]; od;
			od;
			return mat;
		end);
# lists: logic
	InstallMethod( Count,
		[IsList,IsFunction],
		function( l, p )
		local c, x;
		c := 0;
		for x in l do
			if p(x) then c := c+1; fi; od;
		return c;
		end);
	InstallMethod( FilteredNot,
		[IsList,IsFunction],
		function( list, boolFn )
		return Filtered(list,x->not boolFn(x)); end
		);
	InstallMethod( All,
		[IsList],
		L -> ForAll(L,function(l)
			if IsList(l) then return All(l);
			else return l; fi; end)
		);
	InstallMethod( All,
		[IsBool],
		IdFunc
		);
	InstallMethod( Any,
		[IsList],
		L -> ForAny(L,IdFunc)
		);
	InstallMethod( Any,
		[IsBool],
		IdFunc
		);

# lists: comprehension
	InstallMethod( Recursive,
		[IsFunction],
		f -> function( X )
		if IsList(X) then
			return List(X,Recursive(f));
		else
			return f(X); fi;
		end);

# lists: ordering
	InstallMethod( Sorted,
		[IsList,IsFunction],
		function( L,f )
		local M;
		M := ShallowCopy(L);
		SortBy(M,f);
		return M;
		end);
	InstallMethod( Sorted,
		[IsList],
		L -> Sorted(L,IdFunc) );
	InstallMethod( RecursiveSorted,
		[IsObject],
		function( X )
		if IsList(X)
		then return Sorted(List(X,RecursiveSorted));
		else return X; fi;
		end);
	InstallMethod( PartitionBy,
		[IsList,IsFunction],
		function( Set, fn )
			local values, partition, s, v, p;
			Set := ShallowCopy(Set);
			values := [];
			partition := [];
			while not IsEmpty(Set) do
				s := Remove(Set);
				v := fn(s);
				p := Position(values,v);
				if p = fail then
					Add(values,v);
					Add(partition,[v,[s]]);
				else
					Add(partition[p][2],s); fi;
			od;
			return partition;
		end);
	InstallMethod( SortedTo,
		[IsList,IsFunction,IsList],
		function( A, f, B )
			local P, R, i, x;
			P := PartitionBy( A, f );
			R := [];
			for i in [1..Length(B)] do
				x := FirstPosition(P,p->p[1] = B[i]);
				if x = fail then R[i] := Zero(A[1]);
				else R[i] := Remove(P,x); fi;
			od;
			if not IsEmpty(P) then return fail; fi;
			return R;
		end);

# dict
	InstallMethod( CreateDictionary,
		[IsList,IsFunction],
		function( dom, f )
		local d, x;
		if IsEmpty(dom) then d := NewDictionary(false,true,[]);
		else d := NewDictionary(false,true,dom); fi; # unclear bug
		for x in dom
		do AddDictionary(d,x,f(x)); od;
		return d;
		end
		);
	InstallMethod( CreateDictionary,
		[IsList,IsList],
		function( dom, im )
		local d, x;
		d := NewDictionary(false,true,dom);
		for x in [1..Length(dom)]
		do AddDictionary(d,dom[x],im[x]); od;
		return d;
		end
		);
	InstallMethod( CreateDictionary,
		[IsList],
		function( pairs )
		local d, x;
		d := NewDictionary(false,true,List(pairs,p->p[1]));
		for x in [1..Length(pairs)]
		do AddDictionary(d,pairs[x][1],pairs[x][2]); od;
		return d;
		end
		);
	InstallMethod( ViewString,
		[IsDictionary],
		D -> "dictionary"
		);

# actions
	InstallMethod( OnPointsRecursive,
		[IsObject,IsMultiplicativeElementWithInverse],
		function( omega, g )
		return Recursive(o -> OnPoints(o,g))(omega);
		end
		);

# this one is tough to name
	InstallMethod( Mult,
		[IsVectorSpace,IsVectorSpace,IsList],
		function( S, T, Tbl )
		return function(x,y)
			local i, j, z;
			if IsAttrVector(x) then x := Vector(x); fi;
			if IsAttrVector(y) then y := Vector(y); fi;
			z := ShallowCopy(Zero(T));
			for i in [1..Dimension(S)] do
				if not (IsZero(x[i]) or IsZero(y[i])) then
					if not IsBound(Tbl[i][i]) then return fail; # necessary?
					else z := z + x[i]*y[i]*Tbl[i][i]; fi;
				fi;
				for j in [1..i-1] do
					if (not IsZero(x[i]) and not IsZero(y[j]))
					then
						if not IsBound(Tbl[i][j]) then return fail; # necessary?
						else z := z + x[i]*y[j]*Tbl[i][j]; fi;
					fi;
					if (not IsZero(x[j]) and not IsZero(y[i])) 
					then
						if not IsBound(Tbl[j][i]) then return fail; # necessary?
						else z := z + x[j]*y[i]*Tbl[j][i]; fi;
					fi;
				od;
			od;
			return z;
			end;
		end
		);
	InstallMethod( MultComm,
		[IsVectorSpace,IsVectorSpace,IsList],
		function( S, T, Tbl )
		return function(x,y)
			local i, j, z;
			if IsAttrVector(x) then x := Vector(x); fi;
			if IsAttrVector(y) then y := Vector(y); fi;
			z := ShallowCopy(Zero(T));
			for i in [1..Dimension(S)] do
				if not (IsZero(x[i]) or IsZero(y[i])) then
					if not IsBound(Tbl[i][i]) then return fail; # necessary?
					else z := z + x[i]*y[i]*Tbl[i][i]; fi;
				fi;
				for j in [1..i-1] do
					if (not IsZero(x[i]) and not IsZero(y[j]))
					or (not IsZero(x[j]) and not IsZero(y[i])) 
					then
						if not IsBound(Tbl[i][j]) then return fail; # necessary?
						else z := z + (x[i]*y[j]+x[j]*y[i])*Tbl[i][j]; fi;
					fi;
				od;
			od;
			return z;
			end;
		end
		);
	InstallMethod( MultNaive,
		[IsList,IsList,IsList],
		function( x,y,tbl )
		local i, j, z;
		z := ZeroMutable(tbl[1][1]);
		for i in [1..Length(x)] do
			if not (IsZero(x[i]) or IsZero(y[i]))
			then z := z + x[i]*y[i]*tbl[i][i]; fi;
			for j in [1..i-1] do
				if (not IsZero(x[i]) and not IsZero(y[j]))
				or (not IsZero(x[j]) and not IsZero(y[i])) 
				then z := z + (x[i]*y[j]+x[j]*y[i])*tbl[i][j]; fi;
			od;
		od;
		return z;
		end
		);
	InstallGlobalFunction( InField,
		function( a )
		local i, l;
		if a = fail
			then return fail;
		elif IsList(a) then
			l := [];
			for i in [1..Length(a)] do
				l[i] := InField(a[i]);
				if l[i] = fail then return fail; fi; #fail asap
			od;
			return l;
		elif IsFFE(a) or IsCyc(a)
			then return a;
		elif IsConstantRationalFunction(a) then 
			return Value(a,[IndeterminateOfUnivariateRationalFunction(a)],[0]);
		else return fail; fi;
		end
	);

# user
	InstallMethod( UserChoice,
		[IsString,IsList],
		function( Q,Opt )
		local ans;
		Print(Q,"\n");
		while true do
			ans := InputFromUser(); ## todo: make it so user can type char
			if ans in Opt then return ans;
			else Print("what's that? Your options are ",
				JoinStringsWithSeparator(List(Opt,String),", "),":\n"); fi;
		od;
		end
		);

# profiling
	InstallMethod( ElapseStr,
		[IsPosInt],
		function( t )
		local c,s,r,u;
		s := Runtime() - t;
		r := "";
		u := "ms";
		c := "";
		if s > 1000 then
			s := QuoInt(s,1000);
			u := "s";
			if s > 120 then
				s := QuoInt(s,60);
				u := "m";
				if s > 120 then
					r := s mod 60;
					s := QuoInt(s,60);
					c := ":";
					u := "h:m";
					if s > 24 then
						r := s mod 24;
						s := QuoInt(s,24);
						c := ".";
						u := "d.h";
		fi;fi;fi;fi;
		return Concatenation(PrintString(s),c,PrintString(r)," ",u);
		end
	);
	InstallMethod( InfoPro,
		[IsString,IsPosInt],
		function( str, time )
		if InfoLevel(pro)>2 or Runtime() - time > 30000
		then Info( pro, 1, str, ": ", ElapseStr(time) ); fi;
		end
	);
###############################################################################

																# old code
###############################################################################
#	RecursiveAnd := f -> function( X )
#		if IsList(X)
#		then return ForAll(Flat(Recursive(f)(X)),IdFunc);
#		else return f(X); fi; end;
#	RecForAny := function( X, f )
#		if IsList(X) then return ForAny(X,x->RecForAny(x,f));
#		else return f(X); fi; end;
#	OnPtsRec := function( omega, g )
#		return Recursive(o -> OnPoints(o,g))(omega);
#	end;
#	TryFns := function( l, arg )
#	# list[arg -> X], arg -> X
#		local fn, x;
#		while not IsEmpty(l) do
#			fn := Remove(l,1);
#			x := CallFuncList(fn,arg);
#			if x <> fail then
#				return x; fi;
#		od;
#		return fail;
#	end;
#	# compute Size(Flat(L))
#	ReLength := function( L )
#		if IsList( L ) then return Sum(L,ReLength);
#		else return 1; fi;
#	end;
#	# find highest list position with nonzero entry
#	RecHasComponents := function( R, N )
#	# rec, list[..list[str]..] -> bool
#		if not IsRecord(R) then return fail; fi;
#		return ForAll(N,function(n)
#			if IsString(n) then return IsBound(R.(n));
#			else return RecHasComponents(R.(n[1]),n[2]); fi;
#			end);
#	end;
#	SubRecord := function( R, Names ) # like intersection,
#	# rec, list[..list[str]..] -> rec # result not guaranteed
#		local nom,n;										# to contain all Names
#		R := StructuralCopy(R);
#		nom := List(Names,function(x)
#			if IsString(x) then return x;
#			else return x[1]; fi; end);
#		for n in Difference(RecNames(R),nom) do
#			Unbind(R.(n)); od;
#		for n in Filtered(Names,x -> not IsString(x)) do
#			R.(n[1]) := SubRecord(R.(n[1]),n[2]); od;
#		return R;
#	end;
#	AddToRecord := function( arg )
#		local R, i;
#		R := StructuralCopy(arg[1]);
#		for i in [1..(Length(arg)-1)/2] do
#			R.(arg[2*i]) := arg[2*i+1]; od;
#		return R;
#	end;
#	RecordBySchema := schema -> function(x)
#		local r, s;
#		r := rec();
#		for s in schema
#		do r.(s[1]) := s[2](x); od;
#		return r; end;
#	tail := list -> list{[2..Length(list)]};
#	Joiner := function( A, x, B )
#		if IsEmpty(B) then return A;
#		elif IsEmpty(A) then return Joiner(B[1],x,tail(B));
#		else return Joiner(Concatenation( A, x, B[1] ),x,tail(B)); fi; end;
#	ConcatBy := function( list, div )
#		return Joiner([],div,list); end;
#	Compose := function( arg )
#		if IsEmpty(arg) then return IdFunc;
#		elif Length(arg) = 1 then return x -> arg[1](x);
#		else return x -> arg[1](CallFuncList(Compose,tail(arg))(x)); fi; end;
#	SetSubtraction := function( A, B )
#		local Adash;
#		Adash := ShallowCopy(A);
#		SubtractSet(Adash,B);
#		return Adash;
#	end;
#	All := L -> ForAll(L,IdFunc);
#	Any := L -> ForAny(L,IdFunc);
#	SOB := function(i,V)
#		local v;
#		if IsVectorSpace(V) then v := ShallowCopy(Zero(V));
#		else v := List([1..V],i->0); fi;
#		v[i] := 1;
#		return v;
#	end;
#	Projectify := function( v )
#		local p;
#		p := FirstPosition(v,x->not IsZero(x));
#		if p = fail then return v;
#		else return v/v[p]; fi; end;
#	VectorSupport := v -> List(v,function(x)
#		if IsZero(x) then return x; else return 1; fi; end);
#	CartesianWithoutDiagonal := function( A, B )
#		local r, i, j;
#		r := [];
#		for i in [1..Length(A)] do for j in [1..Length(B)] do
#			if A[i] <> B[j] then
#				Add(r,Set([A[i],B[j]])); fi; od; od;
#		return r;
#	end;
#
####
## strings
#	PrintStringGroupHom := function( f )
#	# (permgp -> gp) -> str
#		return Concatenation(
#			"GroupHomomorphismByImagesNC( ",
#			PrintString( Source(f) ),
#			", ",
#			PrintString( Image(f) ),
#			", ",
#			PrintString(GeneratorsOfGroup( Source(f) )),
#			", ",
#			PrintString(List(GeneratorsOfGroup(Source(f)),g -> Image(f,g))),
#			" )"
#		);
#	end;
#	#InstallMethod( PrintString,PrintStringGroupHom,[IsGroupHomomorphism] );
#	PrintStringYo := x->"";
#	PrintStringRecord := function( R )
#		local txt, name;
#		txt := "rec( ";
#		for name in RecNames(R) do
#			txt := Concatenation(txt,"\n\t",name," := ",PrintStringYo(R.(name)),",");
#		od;
#		Remove(txt);
#		txt := Concatenation(txt,"\n)");
#		return txt;
#	end;
#	PrintStringYo := function( X )
#		if IsRecord(X) then
#			return PrintStringRecord(X);
#		elif IsGroupHomomorphism(X) then
#			return PrintStringGroupHom(X);
#		else
#			return PrintString(X);
#		fi;
#	end;
#
####
## gap stuff
#	MinlError := function( arg )
#		local NormalOnBreakMessage, NormalOnBreak;
#		NormalOnBreakMessage := OnBreakMessage;
#		NormalOnBreak := OnBreak;
#		OnBreakMessage := function()
#			OnBreakMessage := NormalOnBreakMessage; end;
#		OnBreak := function()
#			OnBreak := NormalOnBreak; end;
#		CallFuncList(Error,arg);
#	end;
#
#	DeclareInfoClass( "Pro" ); SetInfoLevel( Pro, 2 );
#	InfoPro := function(arg)
#		local time, str;
#		time := Remove(arg);
#		str := Concatenation(List(arg,String));
#		if Runtime()-time > 30000
#		then Info(Pro,1,str,": ",ElapseStr(time)); fi; end;
