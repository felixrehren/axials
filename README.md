# Axial algebras and representations
## a `GAP` package

This package is built to work with so-called axial algebras:
a class of nonassociative algebras
carrying representations of transposition groups.
A particular application is to Majorana theory and hence the Monster.

It requires the Transposition Groups package,
available at http://github.com/felixrehren/trgps.

To set up the package,
install the folder `axials` in your `GAP` packages directory.
For me, that's in `~/.gap/pkg/`.
This is everything.

In `GAP`, load the package with the command `LoadPackage("axials");`.
Here are some sample commands.

    Vir43 := VirasoroFusion(4,3);
    Fields( Vir43 );
    Fuse( V43 )( 1/4,1/4 );

    GetAxialRep( Vir43 );
    R := GetAxialRep( Vir43, Dih(4) )[2];
    FindForm( R );
    CentralCharge( Axes(R)[1] );
    Idempotents( Alg(R) );

    T := TranspositionGroup( Sym(3), [(1,2)] );
    R := FindUniversalAxialRep( T, Vir43 );
    a := Axes(R)[1];
    Eigenspaces(a);
    Rs := Explode( R );
    List( Rs, RecogniseShape );
  
    TT := GroupToTrgps( Sym(4), 6 );
    SS := Shapes( TT[1], MajoranaSakuma );
    RR := List( SS, S -> FindAxialRep( S, Vir43 ) );
