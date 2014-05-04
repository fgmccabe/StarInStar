ecoGame is package{
  import genes;

  type gene is explore or photo or herbivore or carnivore or aggression or progeny;

  type gender is male or female;

  type pheno is pheno{
    energy has type float;
    genes has type map of (gene,float);
    position has type (integer,integer);
    sex has type gender;
  } or dead;

  allGenes is list of {explore; photo; herbivore; carnivore ; aggression; progeny};

  newCreature(X,Y) is pheno{
    energy = random(10.0);
    genes = map of { all (G,V) where G in allGenes and V bound to random(1.0) };
    position = (X,Y);
    sex = (random(1.0)>0.5?male|female);
  }

  sunLight is 0.01;
  death is 0.02;

  updateEnergy(P matching pheno{energy=E;genes=G}) is valof{
    nEnergy is E+sunLight*G[photo]-E*G[aggression];

    valis nEnergy<death?dead|
	P substitute{energy=nEnergy}
  };

  updatePosition(Cr matching pheno{genes=G;position=(X,Y)}) is valof{
    deltaX is ((random(10.0)-5.0)*G[explore]);
    X1 is limit(X+deltaX as integer,100);
    deltaY is ((random(10.0)-5.0)*G[explore]);
    Y1 is limit(Y+deltaY as integer,100);
    valis Cr substitute { position=(X1,Y1) }
  }

  limit(X,L) where X<0 is 0;
  limit(X,L) where X>L is L;
  limit(X,_) default is X;

  main() do {
    var C1 := newCreature(0,1);
    var C2 := newCreature(1,2);

    logMsg(info,"C1=$C1");
    logMsg(info,"C2=$C2");

    while C1!=dead do{
      logMsg(info,"C1 now $(C1.position)");
      C1 := updateEnergy(updatePosition(C1));
    }
  }
}
