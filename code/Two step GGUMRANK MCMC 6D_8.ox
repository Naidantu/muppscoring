#include <oxstd.h> 
#include <oxprob.h>
#include <oxfloat.h>

decl seed=68820;	  //replication 1
decl J=24;	//Number of blocks;
decl N=800;  //Sample size;
decl D=6;	//Number of theta dimensions
decl S=48;	//Number of unique statements;
decl datafile="0.3responsedata68800rep20.txt";	  //File containing the space-delimited response data;
decl pairmap="PairMap68.txt";	  //File containing the statement #s associated with each pair;
decl thetaspec="StateDim68.txt";	  //File containing the statement dimensions;
decl parinits="0.3TwoStepParResults68800rep20.txt";	  //File containing initial values for alpha | delta | tau;
//add for accuracy stats
decl theta_file="0.3GenThetas68800rep20.txt";	//Read theta from GGUMRANK GEN;
decl pars="ParVals68.txt";	  //Read File containing parameter values for alpha | beta;

decl maxmins=720; //Maximum # of minutes for estimation to run;
decl Counter=1000;		//After how many updates do you want to receive notification?;
decl it=50000,burn=25000;	   //Number of total iterations  &  how many should be used as burn-in;
decl chains=3;      //Number of chains to be ran simultaneously;
decl choice=0;		// 0=pair; 1=triplet; 2=quad
decl EstPar=0;	//1=Estimate statement parameters; 0=Do not estimate parameters (uses the specified initial parameter file for scoring only)
decl EstCor=1;	//Allow the thetas to correlate during estimation;
decl EstVar=0;	//Allow the population variance to vary (estimates a full variance-covariance matrix);
decl EstMean=0;	//Allow the population mean to vary;

decl outputparresults=0;		//1=Output statement parameter results to file, 0=Do not output;
decl parresultfile="ParResults68.txt";  //File name for statement parameter results
decl outputpopresults=0;		//1=Output population parameter (means, variance, covariance) results to file, 0=Do not output;
decl popresultfile="PopulationResults.txt";  //File name for population parameter results
decl outputtheta=1;		//1=Output theta estimates to file, 0=Do not output;
decl thetafile="0.3TwoStepThetaEsts68800rep20.txt";  //File name for estimated thetas


//Variables defining the 4-parameter beta parameter for statement prior distributions;
//Defined by two shape parameters, a & b, with a minimum (min) and maximum (max) value range;
//Statement discrimination: Alpha parameter
//Read from file:		/ADD STATE # in first column of prior file.
decl AlphaPriorFile="AlphaPriors68.txt";
decl DeltaPriorFile="DeltaPriors68.txt";
decl TauPriorFile="TauPriors68.txt";

//Candidate distribution SDs. To be adjusted by user: High acceptance rates = increase the SD, Low acceptance rate = decrease the SD;	
decl cand_cov=.05;  //The group covariance/correlation sampling distribution standard deviation
decl cand_var=.15;  //The group variance candidate sampling distribution standard deviation
decl cand_mn=.15;  //The group mean candidate sampling distribution standard deviation
decl cand_th=.30;  //The theta candidate sampling distribution standard deviation
decl cand_a=.18;  //The statement alpha candidate sampling distribution standard deviation
decl cand_d=.16;  //The statement delta candidate sampling distribution standard deviation
decl cand_t=.16;  //The statement tau candidate sampling distribution standard deviation

//Various global variables to used in estimation;
decl time0, time1;
decl thcov0,thvar0,mn0,theta0,alpha0,delta0,tau0;
decl thspec,pairspec,pairapp,nappear,nmax;
decl Alphaa, Alphab, Alphamin, Alphamax;
decl Deltaa, Deltab, Deltamin, Deltamax;
decl Taua, Taub, Taumin, Taumax;
decl apriors,dpriors,tpriors;
decl X;
decl X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12;
decl X13,X14,X15,X16,X17,X18,X19,X20,X21,X22,X23,X24;
decl acptalpha,acptdelta,acpttau,acpttheta,acptthcov,acptmn;
decl acc,accind;


//==========  Begin program functions =============;
mvnpdf(const x,mu,cov){ //Procedure to obtain multivariate normal pdf values;
	decl y=(x-mu)';
	decl d=y'*invert(cov)*y;
	decl p=rows(cov);
	decl con=M_2PI^(p/2)*sqrt(determinant(cov));
	return diagonal(exp(-0.5*d)/con)';
}		 

randmn(const m,c,n){ //Procedure for multivariate normal draws;
	//m = row vector of means =<mean1, mean2, .. >;
	//c = covariance matrix;
	//n = rows (people);
	return m + rann(n, columns(m)) * choleski(c)';
}		 

//Single-statement probabilities(GGUM), returns a NxS matrix of P;
SSPr(const a,d,t,th){
	decl tmp1=1+exp(3*th.*a'-3*ones(N,1)*(a'.*d'));
	decl Ltmp2=exp(th.*a'-ones(N,1)*(a'.*d')-ones(N,1)*(a'.*t'));
	decl Rtmp2=exp(2*th.*a'-2*ones(N,1)*(a'.*d')-ones(N,1)*(a'.*t'));
	decl tmp2=Ltmp2+Rtmp2;
	return((tmp2)./(tmp1+tmp2));
}

//Function that calculates the "Pair" probability/likelihood for a given set of GGUM-RANK responses;
Pair(const a, d, t, th, tmpthspec, tmpspec, sJ, var){
		//a, d, t, th = Alpha, delta, tau & theta parameters;
		//tmpthsp = Dimension associated with each statement (Statement Dimension);
		//tmpspec = pair specification map for the given pairs (Pairmap);
		//sJ = numer of pairs to be examined;
		//var = # of possibility of rank-order response
	decl jS=rows(a); //Number of unique statements contained in the pairs;
	//Populate a NxjS matrix with the theta associated with the statement for each person;
	decl thtemp=zeros(N,jS);
	for(decl i=0; i<N; i++){
		for(decl j=0; j<jS; j++){
			thtemp[i][j]=th[i][tmpthspec[j]];
		}
	}
	//Obtain the P(1) probabilities for each person on each statement;
	decl P=SSPr(a,d,t,thtemp);
	//Calculate the NxJ matrix of GGUM-RANK P(s>t) probabilities for each the pairs;
	decl tmpPR=zeros(N,sJ);

	for(decl j=0; j<sJ; j++){
		decl pst=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][1]]);
		decl pts=P[][tmpspec[j][1]].*(1-P[][tmpspec[j][0]]);
		if (var == 1)
			{tmpPR[][j]=pst./(pst+pts);}  //probability for rank-order response, A>B
		else if (var == 2)
			{tmpPR[][j]=pts./(pst+pts);}  //probability for rank-order response, B>A		
	}
	return(tmpPR);
}

//Function that calculates the "Triplet" probability/likelihood for a given set of GGUM-RANK responses;
Triplet(const a, d, t, th, tmpthspec, tmpspec, sJ, var){
	decl jS=rows(a); //Number of unique statements contained in the pairs;
	//Populate a NxjS matrix with the theta associated with the statement for each person;
	decl thtemp=zeros(N,jS);
	for(decl i=0; i<N; i++){
		for(decl j=0; j<jS; j++){
			thtemp[i][j]=th[i][tmpthspec[j]];
		}
	}
	//Obtain the P(1) probabilities for each person on each statement;
	decl P=SSPr(a,d,t,thtemp);
	//Calculate the NxJ matrix of GGUM-RANK P(s>t) probabilities for each the Triplets;
	decl tmpPR=zeros(N,sJ);

	for(decl j=0; j<sJ; j++){
		decl pa=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]); //100
		decl pb=(1-P[][tmpspec[j][0]]).*(P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]);//010
		decl pc=(1-P[][tmpspec[j][0]]).*(1-P[][tmpspec[j][1]]).*(P[][tmpspec[j][2]]);//001
		decl pab=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][1]]);  //10x
		decl pba=P[][tmpspec[j][1]].*(1-P[][tmpspec[j][0]]);  //01x
		decl pac=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][2]]);  //1x0
		decl pca=P[][tmpspec[j][2]].*(1-P[][tmpspec[j][0]]);  //0x1
		decl pbc=P[][tmpspec[j][1]].*(1-P[][tmpspec[j][2]]);  //x10
		decl pcb=P[][tmpspec[j][2]].*(1-P[][tmpspec[j][1]]);  //x01

		if (var == 3)
			{tmpPR[][j]=pa./(pa+pb+pc).*(pbc./(pbc+pcb));}//A>B>C
		else if (var == 4)		  
				{tmpPR[][j]=pa./(pa+pb+pc).*(pcb./(pbc+pcb));}//A>C>B
		else if (var == 5)		  
				{tmpPR[][j]=pb./(pa+pb+pc).*(pac./(pac+pca));}//B>A>C
		else if (var == 6)	     
				{tmpPR[][j]=pb./(pa+pb+pc).*(pca./(pac+pca));}//B>C>A
		else if (var == 7)		  
				{tmpPR[][j]=pc./(pa+pb+pc).*(pab./(pab+pba));}//C>A>B
		else if (var == 8)	      
				{tmpPR[][j]=pc./(pa+pb+pc).*(pba./(pab+pba));}//C>B>A
	}
	return(tmpPR);
}


//Function that calculates the "Quad" probability/likelihood for a given set of GGUM-RANK responses;
Quad(const a, d, t, th, tmpthspec, tmpspec, sJ, var){
	decl jS=rows(a); //Number of unique statements contained in the Quads;
	decl thtemp=zeros(N,jS);
	for(decl i=0; i<N; i++){
		for(decl j=0; j<jS; j++){
			thtemp[i][j]=th[i][tmpthspec[j]];
		}
	}
	decl P=SSPr(a,d,t,thtemp);
	decl tmpPR=zeros(N,sJ);
	for(decl j=0; j<sJ; j++){
		decl pa=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]).*(1-P[][tmpspec[j][3]]); //1000
		decl pb=(1-P[][tmpspec[j][0]]).*(P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]).*(1-P[][tmpspec[j][3]]);//0100
		decl pc=(1-P[][tmpspec[j][0]]).*(1-P[][tmpspec[j][1]]).*(P[][tmpspec[j][2]]).*(1-P[][tmpspec[j][3]]);//0010
		decl pd=(1-P[][tmpspec[j][0]]).*(1-P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]).*(P[][tmpspec[j][3]]);//0001
		decl pa1=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][2]]).*(1-P[][tmpspec[j][3]]); //1x00
		decl pa2=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][3]]); //10x0
		decl pa3=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]); //100x
		decl pb1=(1-P[][tmpspec[j][2]]).*(P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][3]]); //x100
		decl pb2=(1-P[][tmpspec[j][0]]).*(P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][3]]); //01x0
		decl pb3=(1-P[][tmpspec[j][0]]).*(P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]); //010x
		decl pc1=(1-P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][3]]).*(P[][tmpspec[j][2]]); //x010
		decl pc2=(1-P[][tmpspec[j][0]]).*(1-P[][tmpspec[j][3]]).*(P[][tmpspec[j][2]]); //0x10
		decl pc3=(1-P[][tmpspec[j][0]]).*(1-P[][tmpspec[j][1]]).*(P[][tmpspec[j][2]]); //001x
		decl pd1=(1-P[][tmpspec[j][1]]).*(1-P[][tmpspec[j][2]]).*(P[][tmpspec[j][3]]); //x001
		decl pd2=(1-P[][tmpspec[j][0]]).*(1-P[][tmpspec[j][2]]).*(P[][tmpspec[j][3]]); //0x01
		decl pd3=(1-P[][tmpspec[j][0]]).*(1-P[][tmpspec[j][1]]).*(P[][tmpspec[j][3]]); //00x1
		decl pab=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][1]]);  //10xx
		decl pba=P[][tmpspec[j][1]].*(1-P[][tmpspec[j][0]]);  //01xx
		decl pac=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][2]]);  //1x0x
		decl pca=P[][tmpspec[j][2]].*(1-P[][tmpspec[j][0]]);  //0x1x
		decl pbc=P[][tmpspec[j][1]].*(1-P[][tmpspec[j][2]]);  //x10x
		decl pcb=P[][tmpspec[j][2]].*(1-P[][tmpspec[j][1]]);  //x01x
		decl pad=P[][tmpspec[j][0]].*(1-P[][tmpspec[j][3]]);  //1xx0
		decl pda=P[][tmpspec[j][3]].*(1-P[][tmpspec[j][0]]);  //0xx1
		decl pbd=P[][tmpspec[j][1]].*(1-P[][tmpspec[j][3]]);  //x1x0
		decl pdb=P[][tmpspec[j][3]].*(1-P[][tmpspec[j][1]]);  //x0x1
		decl pcd=P[][tmpspec[j][2]].*(1-P[][tmpspec[j][3]]);  //xx10
		decl pdc=P[][tmpspec[j][3]].*(1-P[][tmpspec[j][2]]);  //xx01
		if (var == 9)
			{tmpPR[][j]=pa./(pa+pb+pc+pd).*(pb1./(pb1+pc1+pd1)).*(pcd./(pcd+pdc));}  //A>B>C>D
		else if (var == 10)		
				{tmpPR[][j]=pa./(pa+pb+pc+pd).*(pb1./(pb1+pc1+pd1)).*(pdc./(pcd+pdc));}  //A>B>D>C
		else if (var == 11)		  
				{tmpPR[][j]=pa./(pa+pb+pc+pd).*(pc1./(pb1+pc1+pd1)).*(pbd./(pbd+pdb));}  //A>C>B>D
		else if (var == 12)	 
				{tmpPR[][j]=pa./(pa+pb+pc+pd).*(pc1./(pb1+pc1+pd1)).*(pdb./(pbd+pdb));}  //A>C>D>B
		else if (var == 13)		 
				{tmpPR[][j]=pa./(pa+pb+pc+pd).*(pd1./(pb1+pc1+pd1)).*(pbc./(pbc+pcb));}  //A>D>B>C
		else if (var == 14)	 
				{tmpPR[][j]=pa./(pa+pb+pc+pd).*(pd1./(pb1+pc1+pd1)).*(pcb./(pbc+pcb));}  //A>D>C>B
		else if (var == 15)		
				{tmpPR[][j]=pb./(pa+pb+pc+pd).*(pa2./(pa2+pc2+pd2)).*(pcd./(pcd+pdc));}  //B>A>C>D
		else if (var == 16)		  
				{tmpPR[][j]=pb./(pa+pb+pc+pd).*(pa2./(pa2+pc2+pd2)).*(pdc./(pcd+pdc));}  //B>A>D>C
		else if (var == 17)	
				{tmpPR[][j]=pb./(pa+pb+pc+pd).*(pc2./(pa2+pc2+pd2)).*(pad./(pad+pda));}  //B>C>A>D
		else if (var == 18)		 
				{tmpPR[][j]=pb./(pa+pb+pc+pd).*(pc2./(pa2+pc2+pd2)).*(pda./(pad+pda));}  //B>C>D>A
		else if (var == 19)	
				{tmpPR[][j]=pb./(pa+pb+pc+pd).*(pd2./(pa2+pc2+pd2)).*(pac./(pac+pca));}  //B>D>A>C
		else if (var == 20)		
				{tmpPR[][j]=pb./(pa+pb+pc+pd).*(pd2./(pa2+pc2+pd2)).*(pca./(pac+pca));}  //B>D>C>A
		else if (var == 21)	
				{tmpPR[][j]=pc./(pa+pb+pc+pd).*(pa3./(pa3+pb3+pd3)).*(pbd./(pbd+pdb));}  //C>A>B>D
		else if (var == 22)	  
				{tmpPR[][j]=pc./(pa+pb+pc+pd).*(pa3./(pa3+pb3+pd3)).*(pdb./(pbd+pdb));}  //C>A>D>B
		else if (var == 23)		
				{tmpPR[][j]=pc./(pa+pb+pc+pd).*(pb3./(pa3+pb3+pd3)).*(pad./(pad+pda));}  //C>B>A>D
		else if (var == 24)	
				{tmpPR[][j]=pc./(pa+pb+pc+pd).*(pb3./(pa3+pb3+pd3)).*(pda./(pad+pda));}  //C>B>D>A
		else if (var == 25)		 
				{tmpPR[][j]=pc./(pa+pb+pc+pd).*(pd3./(pa3+pb3+pd3)).*(pab./(pab+pba));}  //C>D>A>B
		else if (var == 26)		 
				{tmpPR[][j]=pc./(pa+pb+pc+pd).*(pd3./(pa3+pb3+pd3)).*(pba./(pab+pba));}  //C>D>B>A
		else if (var == 27)	 
				{tmpPR[][j]=pd./(pa+pb+pc+pd).*(pa3./(pa3+pb3+pc3)).*(pbc./(pbc+pcb));}  //D>A>B>C
		else if (var == 28)		
				{tmpPR[][j]=pd./(pa+pb+pc+pd).*(pa3./(pa3+pb3+pc3)).*(pcb./(pbc+pcb));}  //D>A>C>B
		else if (var == 29)	
				{tmpPR[][j]=pd./(pa+pb+pc+pd).*(pb3./(pa3+pb3+pc3)).*(pac./(pac+pca));}  //D>B>A>C
		else if (var == 30)		 
				{tmpPR[][j]=pd./(pa+pb+pc+pd).*(pb3./(pa3+pb3+pc3)).*(pca./(pac+pca));}  //D>B>C>A
		else if (var == 31)		 
				{tmpPR[][j]=pd./(pa+pb+pc+pd).*(pc3./(pa3+pb3+pc3)).*(pab./(pab+pba));}  //D>C>A>B
		else if (var == 32)	 
				{tmpPR[][j]=pd./(pa+pb+pc+pd).*(pc3./(pa3+pb3+pc3)).*(pba./(pab+pba));}  //D>C>B>A
	}
	return(tmpPR);
}

//Now calculate "Pair" likelihood based on observed data;
Likelihood1(const a, d, t, th, tmpthspec, tmpspec, sJ, x){ 
	decl p1=Pair(a, d, t, th, tmpthspec, tmpspec, sJ,1);
	decl p2=Pair(a, d, t, th, tmpthspec, tmpspec, sJ,2); 
	decl tmpLike=X1.*log(p1)+X2.*log(p2);
	decl Like = isdotnan(tmpLike) .? 0.0 .: tmpLike; // replace NaN with 0.0;
	return(Like);
}

//Now calculate "Triplet" likelihood based on observed data;
Likelihood2(const a, d, t, th, tmpthspec, tmpspec, sJ, x){ 
	decl p1=Triplet(a, d, t, th, tmpthspec, tmpspec, sJ,3);
	decl p2=Triplet(a, d, t, th, tmpthspec, tmpspec, sJ,4);
	decl p3=Triplet(a, d, t, th, tmpthspec, tmpspec, sJ,5);
	decl p4=Triplet(a, d, t, th, tmpthspec, tmpspec, sJ,6);
	decl p5=Triplet(a, d, t, th, tmpthspec, tmpspec, sJ,7);
	decl p6=Triplet(a, d, t, th, tmpthspec, tmpspec, sJ,8);
	decl tmpLike=X1.*log(p1)+X2.*log(p2)+X3.*log(p3)+X4.*log(p4)+X5.*log(p5)+X6.*log(p6);
	decl Like = isdotnan(tmpLike) .? 0.0 .: tmpLike; // replace NaN with 0.0;
	return(Like);
}

//Now calculate "Quad" likelihood based on observed data;
Likelihood3(const a, d, t, th, tmpthspec, tmpspec, sJ, x){ 
	decl p1=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 9);
	decl p2=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 10);
	decl p3=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 11);
	decl p4=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 12);
	decl p5=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 13);
	decl p6=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 14);
	decl p7=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 15);
	decl p8=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 16);
	decl p9=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 17);
	decl p10=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 18);
	decl p11=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 19);
	decl p12=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 20);
	decl p13=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 21);
	decl p14=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 22);
	decl p15=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 23);
	decl p16=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 24);
	decl p17=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 25);
	decl p18=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 26);
	decl p19=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 27);
	decl p20=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 28);
	decl p21=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 29);
	decl p22=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 30);
	decl p23=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 31);
	decl p24=Quad(a, d, t, th, tmpthspec, tmpspec, sJ, 32);
	decl tmpLike=X1.*log(p1)+X2.*log(p2)+X3.*log(p3)+X4.*log(p4)+X5.*log(p5)+X6.*log(p6).*X7.*log(p7)+X8.*log(p8)+X9.*log(p9)+X10.*log(p10)+X11.*log(p11)+X12.*log(p12).*X13.*log(p13)+X14.*log(p14)+X15.*log(p15)+X16.*log(p16)+X17.*log(p17)+X18.*log(p18).*X19.*log(p19)+X20.*log(p20)+X21.*log(p21)+X22.*log(p22)+X23.*log(p23)+X24.*log(p24);
	decl Like = isdotnan(tmpLike) .? 0.0 .: tmpLike; // replace NaN with 0.0;
	return(Like);
}


initiate(const c){
	//Initial mean for each dimension set to zero;
	mn0=zeros(1,D);
	//Initial variance for each dimension set to one;
	thvar0=ones(1,D);

	//Covariance between dimensions set to zero;
	//Rather than draw a covariance matrix, each covariance term will be examined (easier for tracking);
	thcov0=zeros((D*(D-1))/2);			
	theta0=zeros(N,D); //Initials for theta set to zero;

	//Read in statement parameter initials from file;
	decl inits;
	decl pfile=fopen(parinits);
	fscan(pfile,"%#M",S,3,&inits);
	fclose(pfile);
	alpha0=inits[][0];
	delta0=inits[][1];
	tau0=inits[][2];

//	if(c==0){println("Initial Statement Parameter Values:"); print( "%c", {"Statement", "Alpha", "Delta", "Tau"}, "%cf",{"%8.4g", "%8.4g", "%8.4g", "%8.4g"}, range(1, S, 1)'~alpha0~delta0~tau0);}
}

drawtheta1(){
	decl d0,d1;
	//Draw theta candidates from a multivariate random, with the correlation set to t-1 iteration;
	//Populate the covariance matrix for the MRN draws;
	//Populate the off-diagonal terms with the terms contained in thcov0;
	decl cov=zeros(D,D);
	decl place=0; //counter variable;
	for(decl d=0;d<D;d++){
		for(decl dd=d+1;dd<D;dd++){
			cov[d][dd]=thcov0[place];
			cov[dd][d]=thcov0[place];
			place=place+1;
		}
	}
	cov=thvar0.*ones(D,D).*unit(D)+cov;
	//Convert the covariance matrix to correlation, so that the draws are on the proper scale;
	decl covS=sqrt(diagonal(cov)');
	decl cor=cov./covS'./covS;

	//Now, draw the thetas from a MVN(0,Cor) distribution;
	decl mn=zeros(1,D);
	decl theta1=cand_th*randmn(mn,cor,N)+theta0;

	//Prior for thetas is a MVN
	d0=(sumr(Likelihood1(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+log(mvnpdf(theta0,mn0,cov));
	d1=(sumr(Likelihood1(alpha0, delta0, tau0, theta1, thspec, pairspec, J, X)))+log(mvnpdf(theta1,mn0,cov));

	//Update thetas based on person likelihood;
	acc=d1-d0;
	accind=vecindex(exp(acc).>ranu(N,1));
	theta0[accind][]=theta1[accind][];		   //Only updates indices in the vector where exp(d1-d0) > a random uniform;
	acpttheta[accind]=acpttheta[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
}

drawtheta2(){
	decl d0,d1;
	//Draw theta candidates from a multivariate random, with the correlation set to t-1 iteration;
	//Populate the covariance matrix for the MRN draws;
	//Populate the off-diagonal terms with the terms contained in thcov0;
	decl cov=zeros(D,D);
	decl place=0; //counter variable;
	for(decl d=0;d<D;d++){
		for(decl dd=d+1;dd<D;dd++){
			cov[d][dd]=thcov0[place];
			cov[dd][d]=thcov0[place];
			place=place+1;
		}
	}
	cov=thvar0.*ones(D,D).*unit(D)+cov;
	//Convert the covariance matrix to correlation, so that the draws are on the proper scale;
	decl covS=sqrt(diagonal(cov)');
	decl cor=cov./covS'./covS;

	//Now, draw the thetas from a MVN(0,Cor) distribution;
	decl mn=zeros(1,D);
	decl theta1=cand_th*randmn(mn,cor,N)+theta0;

	//Prior for thetas is a MVN
	d0=(sumr(Likelihood2(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+log(mvnpdf(theta0,mn0,cov));
	d1=(sumr(Likelihood2(alpha0, delta0, tau0, theta1, thspec, pairspec, J, X)))+log(mvnpdf(theta1,mn0,cov));

	//Update thetas based on person likelihood;
	acc=d1-d0;
	accind=vecindex(exp(acc).>ranu(N,1));
	theta0[accind][]=theta1[accind][];		   //Only updates indices in the vector where exp(d1-d0) > a random uniform;
	acpttheta[accind]=acpttheta[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
}

drawtheta3(){
	decl d0,d1;
	//Draw theta candidates from a multivariate random, with the correlation set to t-1 iteration;
	//Populate the covariance matrix for the MRN draws;
	//Populate the off-diagonal terms with the terms contained in thcov0;
	decl cov=zeros(D,D);
	decl place=0; //counter variable;
	for(decl d=0;d<D;d++){
		for(decl dd=d+1;dd<D;dd++){
			cov[d][dd]=thcov0[place];
			cov[dd][d]=thcov0[place];
			place=place+1;
		}
	}
	cov=thvar0.*ones(D,D).*unit(D)+cov;
	//Convert the covariance matrix to correlation, so that the draws are on the proper scale;
	decl covS=sqrt(diagonal(cov)');
	decl cor=cov./covS'./covS;

	//Now, draw the thetas from a MVN(0,Cor) distribution;
	decl mn=zeros(1,D);
	decl theta1=cand_th*randmn(mn,cor,N)+theta0;

	//Prior for thetas is a MVN
	d0=(sumr(Likelihood3(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+log(mvnpdf(theta0,mn0,cov));
	d1=(sumr(Likelihood3(alpha0, delta0, tau0, theta1, thspec, pairspec, J, X)))+log(mvnpdf(theta1,mn0,cov));

	//Update thetas based on person likelihood;
	acc=d1-d0;
	accind=vecindex(exp(acc).>ranu(N,1));
	theta0[accind][]=theta1[accind][];		//Only updates indices in the vector where exp(d1-d0) > a random uniform;
	acpttheta[accind]=acpttheta[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
}


drawbeta1() {
	decl d0,d1;
	decl alpha1=cand_a*rann(S,1)+alpha0;
	decl delta1=cand_d*rann(S,1)+delta0;
	decl tau1=cand_t*rann(S,1)+tau0;

	    //=============  Updates at the pair-level so that the block statement parameters are updated simultaneously ================
		//Create matrices for each set which contains the parameters associated with each pair.
		//Create matrices which contain the values to be assigned to each statement in a pair when calculating priors.
		decl alpha0pair=zeros(J,2),alpha1pair=zeros(J,2);
		decl delta0pair=zeros(J,2),delta1pair=zeros(J,2);
		decl tau0pair=zeros(J,2),tau1pair=zeros(J,2);
		decl Aminprior=zeros(J,2),Amaxprior=zeros(J,2),Aaprior=zeros(J,2),Abprior=zeros(J,2);
		decl Dminprior=zeros(J,2),Dmaxprior=zeros(J,2),Daprior=zeros(J,2),Dbprior=zeros(J,2);
		decl Tminprior=zeros(J,2),Tmaxprior=zeros(J,2),Taprior=zeros(J,2),Tbprior=zeros(J,2);

		//Now, populate those matrices with the parameter values;
		for(decl j=0;j<J;j++){
			alpha0pair[j][0]=alpha0[pairspec[j][0]]; alpha1pair[j][0]=alpha1[pairspec[j][0]];
			alpha0pair[j][1]=alpha0[pairspec[j][1]]; alpha1pair[j][1]=alpha1[pairspec[j][1]];
			Aminprior[j][0]=Alphamin[pairspec[j][0]]; Amaxprior[j][0]=Alphamax[pairspec[j][0]];
			Aminprior[j][1]=Alphamin[pairspec[j][1]]; Amaxprior[j][1]=Alphamax[pairspec[j][1]];
			Aaprior[j][0]=Alphaa[pairspec[j][0]]; Abprior[j][0]=Alphab[pairspec[j][0]];
			Aaprior[j][1]=Alphaa[pairspec[j][1]]; Abprior[j][1]=Alphab[pairspec[j][1]];

			delta0pair[j][0]=delta0[pairspec[j][0]]; delta1pair[j][0]=delta1[pairspec[j][0]];
			delta0pair[j][1]=delta0[pairspec[j][1]]; delta1pair[j][1]=delta1[pairspec[j][1]];
			Dminprior[j][0]=Deltamin[pairspec[j][0]]; Dmaxprior[j][0]=Deltamax[pairspec[j][0]];
			Dminprior[j][1]=Deltamin[pairspec[j][1]]; Dmaxprior[j][1]=Deltamax[pairspec[j][1]];
			Daprior[j][0]=Deltaa[pairspec[j][0]]; Dbprior[j][0]=Deltab[pairspec[j][0]];
			Daprior[j][1]=Deltaa[pairspec[j][1]]; Dbprior[j][1]=Deltab[pairspec[j][1]];

			tau0pair[j][0]=tau0[pairspec[j][0]]; tau1pair[j][0]=tau1[pairspec[j][0]];
			tau0pair[j][1]=tau0[pairspec[j][1]]; tau1pair[j][1]=tau1[pairspec[j][1]];
			Tminprior[j][0]=Taumin[pairspec[j][0]]; Tmaxprior[j][0]=Taumax[pairspec[j][0]];
			Tminprior[j][1]=Taumin[pairspec[j][1]]; Tmaxprior[j][1]=Taumax[pairspec[j][1]];
			Taprior[j][0]=Taua[pairspec[j][0]]; Tbprior[j][0]=Taub[pairspec[j][0]];
			Taprior[j][1]=Taua[pairspec[j][1]]; Tbprior[j][1]=Taub[pairspec[j][1]];
			
		}

		//For Alpha draws
		d0=(sumc(Likelihood1(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((alpha0pair-Aminprior)./(Amaxprior-Aminprior),Aaprior,Abprior)))';
		d1=(sumc(Likelihood1(alpha1, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((alpha1pair-Aminprior)./(Amaxprior-Aminprior),Aaprior,Abprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		alpha0pair[accind][]=alpha1pair[accind][];
		acptalpha[accind]=acptalpha[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the alpha0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			alpha0[pairspec[j][0]]=alpha0pair[j][0];
			alpha0[pairspec[j][1]]=alpha0pair[j][1];
		}


		// For Delta Draws
		d0=(sumc(Likelihood1(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((delta0pair-Dminprior)./(Dmaxprior-Dminprior),Daprior,Dbprior)))';
		d1=(sumc(Likelihood1(alpha0, delta1, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((delta1pair-Dminprior)./(Dmaxprior-Dminprior),Daprior,Dbprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		delta0pair[accind][]=delta1pair[accind][];
		acptdelta[accind]=acptdelta[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the delta0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			delta0[pairspec[j][0]]=delta0pair[j][0];
			delta0[pairspec[j][1]]=delta0pair[j][1];
		}

		// For Tau Draws
		d0=(sumc(Likelihood1(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((tau0pair-Tminprior)./(Tmaxprior-Tminprior),Taprior,Tbprior)))';
		d1=(sumc(Likelihood1(alpha0, delta0, tau1, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((tau1pair-Tminprior)./(Tmaxprior-Tminprior),Taprior,Tbprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		tau0pair[accind][]=tau1pair[accind][];
		acpttau[accind]=acpttau[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the delta0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			tau0[pairspec[j][0]]=tau0pair[j][0];
			tau0[pairspec[j][1]]=tau0pair[j][1];
		}
}

drawbeta2() {
	decl d0,d1;
	decl alpha1=cand_a*rann(S,1)+alpha0;
	decl delta1=cand_d*rann(S,1)+delta0;
	decl tau1=cand_t*rann(S,1)+tau0;


	//=============  Updates at the triplet-level so that the two statement parameters are updated simultaneously ================
		//Create matrices for each set which contains the parameters associated with each triplet.
		//Create matrices which contain the values to be assigned to each statement in a triplet when calculating priors.
		decl alpha0pair=zeros(J,3),alpha1pair=zeros(J,3);
		decl delta0pair=zeros(J,3),delta1pair=zeros(J,3);
		decl tau0pair=zeros(J,3),tau1pair=zeros(J,3);
		decl Aminprior=zeros(J,3),Amaxprior=zeros(J,3),Aaprior=zeros(J,3),Abprior=zeros(J,3);
		decl Dminprior=zeros(J,3),Dmaxprior=zeros(J,3),Daprior=zeros(J,3),Dbprior=zeros(J,3);
		decl Tminprior=zeros(J,3),Tmaxprior=zeros(J,3),Taprior=zeros(J,3),Tbprior=zeros(J,3);

		//Now, populate those matrices with the parameter values;
		for(decl j=0;j<J;j++){
			alpha0pair[j][0]=alpha0[pairspec[j][0]]; alpha1pair[j][0]=alpha1[pairspec[j][0]];
			alpha0pair[j][1]=alpha0[pairspec[j][1]]; alpha1pair[j][1]=alpha1[pairspec[j][1]];
			alpha0pair[j][2]=alpha0[pairspec[j][2]]; alpha1pair[j][2]=alpha1[pairspec[j][2]];		
			Aminprior[j][0]=Alphamin[pairspec[j][0]]; Amaxprior[j][0]=Alphamax[pairspec[j][0]];
			Aminprior[j][1]=Alphamin[pairspec[j][1]]; Amaxprior[j][1]=Alphamax[pairspec[j][1]];
			Aminprior[j][2]=Alphamin[pairspec[j][2]]; Amaxprior[j][2]=Alphamax[pairspec[j][2]];
			Aaprior[j][0]=Alphaa[pairspec[j][0]]; Abprior[j][0]=Alphab[pairspec[j][0]];
			Aaprior[j][1]=Alphaa[pairspec[j][1]]; Abprior[j][1]=Alphab[pairspec[j][1]];
			Aaprior[j][2]=Alphaa[pairspec[j][2]]; Abprior[j][2]=Alphab[pairspec[j][2]];

			delta0pair[j][0]=delta0[pairspec[j][0]]; delta1pair[j][0]=delta1[pairspec[j][0]];
			delta0pair[j][1]=delta0[pairspec[j][1]]; delta1pair[j][1]=delta1[pairspec[j][1]];
			delta0pair[j][2]=delta0[pairspec[j][2]]; delta1pair[j][2]=delta1[pairspec[j][2]];
			Dminprior[j][0]=Deltamin[pairspec[j][0]]; Dmaxprior[j][0]=Deltamax[pairspec[j][0]];
			Dminprior[j][1]=Deltamin[pairspec[j][1]]; Dmaxprior[j][1]=Deltamax[pairspec[j][1]];
			Dminprior[j][2]=Deltamin[pairspec[j][2]]; Dmaxprior[j][2]=Deltamax[pairspec[j][2]];
			Daprior[j][0]=Deltaa[pairspec[j][0]]; Dbprior[j][0]=Deltab[pairspec[j][0]];
			Daprior[j][1]=Deltaa[pairspec[j][1]]; Dbprior[j][1]=Deltab[pairspec[j][1]];
			Daprior[j][2]=Deltaa[pairspec[j][2]]; Dbprior[j][2]=Deltab[pairspec[j][2]];
			
			tau0pair[j][0]=tau0[pairspec[j][0]]; tau1pair[j][0]=tau1[pairspec[j][0]];
			tau0pair[j][1]=tau0[pairspec[j][1]]; tau1pair[j][1]=tau1[pairspec[j][1]];
			tau0pair[j][2]=tau0[pairspec[j][2]]; tau1pair[j][2]=tau1[pairspec[j][2]];
			Tminprior[j][0]=Taumin[pairspec[j][0]]; Tmaxprior[j][0]=Taumax[pairspec[j][0]];
			Tminprior[j][1]=Taumin[pairspec[j][1]]; Tmaxprior[j][1]=Taumax[pairspec[j][1]];
			Tminprior[j][2]=Taumin[pairspec[j][2]]; Tmaxprior[j][2]=Taumax[pairspec[j][2]];
			Taprior[j][0]=Taua[pairspec[j][0]]; Tbprior[j][0]=Taub[pairspec[j][0]];
			Taprior[j][1]=Taua[pairspec[j][1]]; Tbprior[j][1]=Taub[pairspec[j][1]];
			Taprior[j][2]=Taua[pairspec[j][2]]; Tbprior[j][2]=Taub[pairspec[j][2]];
		}

		//For Alpha draws
		d0=(sumc(Likelihood2(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((alpha0pair-Aminprior)./(Amaxprior-Aminprior),Aaprior,Abprior)))';
		d1=(sumc(Likelihood2(alpha1, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((alpha1pair-Aminprior)./(Amaxprior-Aminprior),Aaprior,Abprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		alpha0pair[accind][]=alpha1pair[accind][];
		acptalpha[accind]=acptalpha[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the alpha0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			alpha0[pairspec[j][0]]=alpha0pair[j][0];
			alpha0[pairspec[j][1]]=alpha0pair[j][1];
			alpha0[pairspec[j][2]]=alpha0pair[j][2];
		}


		// For Delta Draws
		d0=(sumc(Likelihood2(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((delta0pair-Dminprior)./(Dmaxprior-Dminprior),Daprior,Dbprior)))';
		d1=(sumc(Likelihood2(alpha0, delta1, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((delta1pair-Dminprior)./(Dmaxprior-Dminprior),Daprior,Dbprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		delta0pair[accind][]=delta1pair[accind][];
		acptdelta[accind]=acptdelta[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the delta0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			delta0[pairspec[j][0]]=delta0pair[j][0];
			delta0[pairspec[j][1]]=delta0pair[j][1];
			delta0[pairspec[j][2]]=delta0pair[j][2];
		}

		// For Tau Draws
		d0=(sumc(Likelihood2(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((tau0pair-Tminprior)./(Tmaxprior-Tminprior),Taprior,Tbprior)))';
		d1=(sumc(Likelihood2(alpha0, delta0, tau1, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((tau1pair-Tminprior)./(Tmaxprior-Tminprior),Taprior,Tbprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		tau0pair[accind][]=tau1pair[accind][];
		acpttau[accind]=acpttau[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the delta0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			tau0[pairspec[j][0]]=tau0pair[j][0];
			tau0[pairspec[j][1]]=tau0pair[j][1];
			tau0[pairspec[j][2]]=tau0pair[j][2];
		}
}

drawbeta3() {
	decl d0,d1;
	decl alpha1=cand_a*rann(S,1)+alpha0;
	decl delta1=cand_d*rann(S,1)+delta0;
	decl tau1=cand_t*rann(S,1)+tau0;

	//=============  Updates at the tetrad-level so that the two statement parameters are updated simultaneously ================
		//Create matrices for each set which contains the parameters associated with each tetrad.
		//Create matrices which contain the values to be assigned to each statement in a tetrad when calculating priors.
		decl alpha0pair=zeros(J,4),alpha1pair=zeros(J,4);
		decl delta0pair=zeros(J,4),delta1pair=zeros(J,4);
		decl tau0pair=zeros(J,4),tau1pair=zeros(J,4);
		decl Aminprior=zeros(J,4),Amaxprior=zeros(J,4),Aaprior=zeros(J,4),Abprior=zeros(J,4);
		decl Dminprior=zeros(J,4),Dmaxprior=zeros(J,4),Daprior=zeros(J,4),Dbprior=zeros(J,4);
		decl Tminprior=zeros(J,4),Tmaxprior=zeros(J,4),Taprior=zeros(J,4),Tbprior=zeros(J,4);

		//Now, populate those matrices with the parameter values;
		for(decl j=0;j<J;j++){
			alpha0pair[j][0]=alpha0[pairspec[j][0]]; alpha1pair[j][0]=alpha1[pairspec[j][0]];
			alpha0pair[j][1]=alpha0[pairspec[j][1]]; alpha1pair[j][1]=alpha1[pairspec[j][1]];
			alpha0pair[j][2]=alpha0[pairspec[j][2]]; alpha1pair[j][2]=alpha1[pairspec[j][2]];
			alpha0pair[j][3]=alpha0[pairspec[j][3]]; alpha1pair[j][3]=alpha1[pairspec[j][3]];
			Aminprior[j][0]=Alphamin[pairspec[j][0]]; Amaxprior[j][0]=Alphamax[pairspec[j][0]];
			Aminprior[j][1]=Alphamin[pairspec[j][1]]; Amaxprior[j][1]=Alphamax[pairspec[j][1]];
			Aminprior[j][2]=Alphamin[pairspec[j][2]]; Amaxprior[j][2]=Alphamax[pairspec[j][2]];
			Aminprior[j][3]=Alphamin[pairspec[j][3]]; Amaxprior[j][3]=Alphamax[pairspec[j][3]];
			Aaprior[j][0]=Alphaa[pairspec[j][0]]; Abprior[j][0]=Alphab[pairspec[j][0]];
			Aaprior[j][1]=Alphaa[pairspec[j][1]]; Abprior[j][1]=Alphab[pairspec[j][1]];
			Aaprior[j][2]=Alphaa[pairspec[j][2]]; Abprior[j][2]=Alphab[pairspec[j][2]];
			Aaprior[j][3]=Alphaa[pairspec[j][3]]; Abprior[j][3]=Alphab[pairspec[j][3]];
			
			delta0pair[j][0]=delta0[pairspec[j][0]]; delta1pair[j][0]=delta1[pairspec[j][0]];
			delta0pair[j][1]=delta0[pairspec[j][1]]; delta1pair[j][1]=delta1[pairspec[j][1]];
			delta0pair[j][2]=delta0[pairspec[j][2]]; delta1pair[j][2]=delta1[pairspec[j][2]];
			delta0pair[j][3]=delta0[pairspec[j][3]]; delta1pair[j][3]=delta1[pairspec[j][3]];
			Dminprior[j][0]=Deltamin[pairspec[j][0]]; Dmaxprior[j][0]=Deltamax[pairspec[j][0]];
			Dminprior[j][1]=Deltamin[pairspec[j][1]]; Dmaxprior[j][1]=Deltamax[pairspec[j][1]];
			Dminprior[j][2]=Deltamin[pairspec[j][2]]; Dmaxprior[j][2]=Deltamax[pairspec[j][2]];
			Dminprior[j][3]=Deltamin[pairspec[j][3]]; Dmaxprior[j][3]=Deltamax[pairspec[j][3]];
			Daprior[j][0]=Deltaa[pairspec[j][0]]; Dbprior[j][0]=Deltab[pairspec[j][0]];
			Daprior[j][1]=Deltaa[pairspec[j][1]]; Dbprior[j][1]=Deltab[pairspec[j][1]];
			Daprior[j][2]=Deltaa[pairspec[j][2]]; Dbprior[j][2]=Deltab[pairspec[j][2]];
			Daprior[j][3]=Deltaa[pairspec[j][3]]; Dbprior[j][3]=Deltab[pairspec[j][3]];
			
			tau0pair[j][0]=tau0[pairspec[j][0]]; tau1pair[j][0]=tau1[pairspec[j][0]];
			tau0pair[j][1]=tau0[pairspec[j][1]]; tau1pair[j][1]=tau1[pairspec[j][1]];
			tau0pair[j][2]=tau0[pairspec[j][2]]; tau1pair[j][2]=tau1[pairspec[j][2]];
			tau0pair[j][3]=tau0[pairspec[j][3]]; tau1pair[j][3]=tau1[pairspec[j][3]];
			Tminprior[j][0]=Taumin[pairspec[j][0]]; Tmaxprior[j][0]=Taumax[pairspec[j][0]];
			Tminprior[j][1]=Taumin[pairspec[j][1]]; Tmaxprior[j][1]=Taumax[pairspec[j][1]];
			Tminprior[j][2]=Taumin[pairspec[j][2]]; Tmaxprior[j][2]=Taumax[pairspec[j][2]];
			Tminprior[j][3]=Taumin[pairspec[j][3]]; Tmaxprior[j][3]=Taumax[pairspec[j][3]];
			Taprior[j][0]=Taua[pairspec[j][0]]; Tbprior[j][0]=Taub[pairspec[j][0]];
			Taprior[j][1]=Taua[pairspec[j][1]]; Tbprior[j][1]=Taub[pairspec[j][1]];
			Taprior[j][2]=Taua[pairspec[j][2]]; Tbprior[j][2]=Taub[pairspec[j][2]];
			Taprior[j][3]=Taua[pairspec[j][3]]; Tbprior[j][3]=Taub[pairspec[j][3]];
		}

		//For Alpha draws
		d0=(sumc(Likelihood3(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((alpha0pair-Aminprior)./(Amaxprior-Aminprior),Aaprior,Abprior)))';
		d1=(sumc(Likelihood3(alpha1, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((alpha1pair-Aminprior)./(Amaxprior-Aminprior),Aaprior,Abprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		alpha0pair[accind][]=alpha1pair[accind][];
		acptalpha[accind]=acptalpha[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the alpha0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			alpha0[pairspec[j][0]]=alpha0pair[j][0];
			alpha0[pairspec[j][1]]=alpha0pair[j][1];
			alpha0[pairspec[j][2]]=alpha0pair[j][2];
			alpha0[pairspec[j][3]]=alpha0pair[j][3];
		}


		// For Delta Draws
		d0=(sumc(Likelihood3(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((delta0pair-Dminprior)./(Dmaxprior-Dminprior),Daprior,Dbprior)))';
		d1=(sumc(Likelihood3(alpha0, delta1, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((delta1pair-Dminprior)./(Dmaxprior-Dminprior),Daprior,Dbprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		delta0pair[accind][]=delta1pair[accind][];
		acptdelta[accind]=acptdelta[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the delta0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			delta0[pairspec[j][0]]=delta0pair[j][0];
			delta0[pairspec[j][1]]=delta0pair[j][1];
			delta0[pairspec[j][2]]=delta0pair[j][2];
			delta0[pairspec[j][3]]=delta0pair[j][3];
		}

		// For Tau Draws
		d0=(sumc(Likelihood3(alpha0, delta0, tau0, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((tau0pair-Tminprior)./(Tmaxprior-Tminprior),Taprior,Tbprior)))';
		d1=(sumc(Likelihood3(alpha0, delta0, tau1, theta0, thspec, pairspec, J, X)))+sumr(log(densbeta((tau1pair-Tminprior)./(Tmaxprior-Tminprior),Taprior,Tbprior)))';
		acc=d1-d0;
		accind=vecindex(exp(acc).>ranu(1,J));
		tau0pair[accind][]=tau1pair[accind][];
		acpttau[accind]=acpttau[accind]+1;  //If value accepted, adds one to the tracking acceptance rate;
		//Change the delta0 vector based on state of the pairs;
		for(decl j=0;j<J;j++){
			tau0[pairspec[j][0]]=tau0pair[j][0];
			tau0[pairspec[j][1]]=tau0pair[j][1];
			tau0[pairspec[j][2]]=tau0pair[j][2];
			tau0[pairspec[j][3]]=tau0pair[j][3];
		}
}


//Procedure to draw and population parameters (mean, variance-covariance);
drawlamda(){
	decl d0,d1;

	//------- First, draw & test means ------
	//Populate the covariance matrix, cov0, with the current state;
	//Populate the off-diagonal terms with the terms contained in thcor0;
	decl cov0=zeros(D,D);	//Creates a DxD matrix with ones on the diagonal;
	decl place=0; //counter variable;
	for(decl d=0;d<D;d++){
		for(decl dd=d+1;dd<D;dd++){
			cov0[d][dd]=thcov0[place];
			cov0[dd][d]=thcov0[place];
			place=place+1;
		}
	}
	cov0=thvar0.*ones(D,D).*unit(D)+cov0;

	//If user selected, draw mean candidates;
	if(EstMean==1){
		decl mn1=cand_mn*rann(1,D)+mn0;

		//Likelihood is P(thetas | MVN(Mn,Cov)), uniform prior means it drops out;
		d0=sumc(log(mvnpdf(theta0,mn0,cov0)));
		d1=sumc(log(mvnpdf(theta0,mn1,cov0)));

		//Update means based on full likelihood;
		acc=d1-d0;
		if(exp(acc).>ranu(1,1)){	//Updates new covariance coefficients where exp(model1-model0) > a random uniform;
			mn0=mn1;
			acptmn=acptmn+1;
		}
	}//End EstMean If;

	//------- Second, draw & test covariance matrix ------;
	if(EstCor==1){
		//Code to draw the covariance coefficents for the thetas. Draws new covariance, and then checks
			//to ensure that the resulting matrix is a positive definite. If no, draws new covariance until so;
		decl cov1=zeros(D,D);	//Creates a DxD matrix with ones on the diagonal;
		decl thcov1;
		decl thvar1=ones(1,D);
		decl covcheck=1;
		oxwarning(0); //Suppresses the warning about decomposition failing, can spam screen.
		do{
			covcheck=1;
			//Draw the covariance candidates;
			thcov1=cand_cov*rann((D*(D-1))/2,1)+thcov0;
			//If variance estimates were asked for, draws those;
			if(EstVar==1){  //If the variance terms were selected to be estimated;
				//Draw the variance candidates;
				thvar1=cand_var*rann(1,D)+thvar0;
			}
	
			//Populate the covariance matrix for the MRN draws;
			//Populate the off-diagonal terms with the new draws contained in thcov1;
			place=0; //counter variable;
			for(decl d=0;d<D;d++){
				for(decl dd=d+1;dd<D;dd++){
					cov1[d][dd]=thcov1[place];
					cov1[dd][d]=thcov1[place];
					place=place+1;
				}
			}
			cov1=thvar1.*ones(D,D).*unit(D)+cov1;
			if(choleski(cov1)==0){
				//println(">>>>>> Cholesky decomposition failed, redrawing covariance matrix <<<<<<");
				covcheck=0;
			}
		}while(covcheck==0);	
		oxwarning(1);	//Turn warnings back on just in case;
	
		//Likelihood is P(thetas | MVN(Mn,Cov)), uniform prior means it drops out;
		d0=sumc(log(mvnpdf(theta0,mn0,cov0)));
		d1=sumc(log(mvnpdf(theta0,mn0,cov1)));
	
		//Update theta covariance based on full likelihood;
		acc=d1-d0;
		if(exp(acc).>ranu(1,1)){	//Updates new covariance coefficients where exp(model1-model0) > a random uniform;
			thcov0=thcov1;
			thvar0=thvar1;
			acptthcov=acptthcov+1;
		}
	}//End EstCor If;


	//------- Optional Third, draw & test variance terms if Cor/Cov terms NOT ESTIMATED ------;
	if(EstCor==0){
		if(EstVar==1){  //If the variance terms were selected to be estimated;
			decl cov1=zeros(D,D);	//Creates a DxD matrix with ones on the diagonal;
			decl thvar1=ones(1,D);
			//Draw the variance candidates;
			thvar1=cand_var*rann(1,D)+thvar0;
			cov1=thvar1.*ones(D,D).*unit(D)+cov1;
	
			//Likelihood is P(thetas | MVN(Mn,Cov)), uniform prior means it drops out;
			d0=sumc(log(mvnpdf(theta0,mn0,cov0)));
			d1=sumc(log(mvnpdf(theta0,mn0,cov1)));
	
			//Update theta covariance based on full likelihood;
			acc=d1-d0;
			if(exp(acc).>ranu(1,1)){	//Updates new covariance coefficients where exp(model1-model0) > a random uniform;
				thvar0=thvar1;
				acptthcov=acptthcov+1;
			}
		}//End EstVar=1 If;
	}//End EstCor=0 If;
}



//===================================================================================================;
//========================================Begin Main Program=========================================;
main()                
{
time0 = timer();
ranseed(seed);

//Early error check: If pairs are updated together, then it assumes no statement repetition.
//Thus, S has to equal J*2;
//If that is not the case, exit the program with a warning;
if(choice==0){
if(S!=J*2){println("ERROR, S not equal to J*2"); exit(1);}
}

if(choice==1){
if(S!=J*3){println("ERROR, S not equal to J*3"); exit(1);}
}

if(choice==2){
if(S!=J*4){println("ERROR, S not equal to J*4"); exit(1);}
}

//Read in actual data
decl file=fopen(datafile);
fscan(file,"%#M",N,J,&X);
fclose(file);

//Output first and last lines of data;
//println("Responses for first line of data");
//print("%8.4g", X[0][]);
//println("Responses for last line of data");
//print("%8.4g", X[N-1][]);

//Create matrix for each option, with 1 of option selected and 0 if option not selected;
if(choice==0){
X1=X.==12; //A>B
X2=X.==21; //B>B
}

if(choice==1){
X1=X.==123; //A>B>C
X2=X.==132; //A>C>B
X3=X.==213; //B>A>C
X4=X.==312; //B>C>A
X5=X.==231; //C>A>B
X6=X.==321; //C>B>A
	
}

if(choice==2){
X1=X.==1234; //A>B>C>D
X2=X.==1243; //A>B>D>C
X3=X.==1324; //A>C>B>D
X4=X.==1423; //A>C>D>B
X5=X.==1342; //A>D>B>C
X6=X.==1432; //A>D>C>B
X7=X.==2134; //B>A>C>D
X8=X.==2143; //B>A>D>C
X9=X.==3124; //B>C>A>D
X10=X.==4123; //B>C>D>A
X11=X.==3142; //B>D>A>C
X12=X.==4132; //B>D>C>A
X13=X.==2314; //C>A>B>D
X14=X.==2413; //C>A>D>B
X15=X.==3214; //C>B>A>D
X16=X.==4213; //C>B>D>A
X17=X.==3412; //C>D>A>B
X18=X.==4312; //C>D>B>A
X19=X.==2341; //D>A>B>C
X20=X.==2431; //D>A>C>B
X21=X.==3241; //D>B>A>C
X22=X.==4231; //D>B>C>A
X23=X.==3421; //D>C>A>B
X24=X.==4321; //D>C>B>A
}



//Read in the statement specifications for the pairs;
if(choice==0){
decl tempspec;
decl mapfile=fopen(pairmap);
fscan(mapfile,"%#M",J,3,&tempspec);
fclose(mapfile);
pairspec=tempspec[][1:2];
	//Recode, because index in Ox begins at position 0, rather than 1;
pairspec=pairspec-1;

//Output statement pairings;
//println("Statement Pairings");
//print( "%c", {"Item", "A", "B"}, "%cf",{"%8.4g", "%8.4g", "%8.4g"}, range(1, J, 1)'~pairspec+1);


//Specify which item pairs each statement appears in;
pairapp=constant(.NaN,S,J);
for(decl s=0;s<S;s++){
	decl col=0;
	for(decl j=0;j<J;j++){
	if(pairspec[j][0]==s||pairspec[j][1]==s){pairapp[s][col]=j;col=col+1;}
	}
}
//Counts how many items a statement appears in;
nappear=sumr(countr(pairapp,<0>));
//println("Number of times each statement appears in a pair");
//print( "%c", {"Statement", "  #appear"}, "%cf",{"%8.4g", "%8.4g"}, range(1, S, 1)'~nappear);

//Determines maximum number of times a statement appears;
nmax=max(nappear);
//println("Maximum number of pairs in which a statement appears");
//println(nmax);
//Deletes empty columns from the where statements appear matrix;
//for(decl j=J;j>nmax-1;j--){pairapp=dropc(pairapp,j);}
//println("Pairwise preference item numbers in which the statement appears:");
//print( "%c", {"Statement", "  Pairs in which statement appearance"}, "%cf",{"%8.4g", "%8.4g"}, range(1, S, 1)'~pairapp+1);

//Second error check: If pairs are updated together, then it assumes no statement repetition.;
	//So, if nappear is larger than 1, error end close;
if(nmax>1){println("ERROR, a statement appears more than once in the pairmap, and pairupdate was set to 1"); exit(1);}
}

//Read in the statement specifications for the triplets;
if(choice==1){
decl tempspec;
decl mapfile=fopen(pairmap);
fscan(mapfile,"%#M",J,4,&tempspec);
fclose(mapfile);
pairspec=tempspec[][1:3];
	//Recode, because index in Ox begins at position 0, rather than 1;
pairspec=pairspec-1;

//Output statement pairings;
println("Triplet Statements");
print( "%c", {"Item", "A", "B", "C"}, "%cf",{"%8.4g", "%8.4g", "%8.4g", "%8.4g"}, range(1, J, 1)'~pairspec+1);


//Specify which item triplets each statement appears in;
pairapp=constant(.NaN,S,J);
for(decl s=0;s<S;s++){
	decl col=0;
	for(decl j=0;j<J;j++){
	if(pairspec[j][0]==s||pairspec[j][1]==s||pairspec[j][2]==s){pairapp[s][col]=j;col=col+1;}
	}
}
//Counts how many items a statement appears in;
nappear=sumr(countr(pairapp,<0>));
println("Number of times each statement appears in a triplets");
print( "%c", {"Statement", "  #appear"}, "%cf",{"%8.4g", "%8.4g"}, range(1, S, 1)'~nappear);

//Determines maximum number of times a statement appears;
nmax=max(nappear);
println("Maximum number of triplets in which a statement appears");
println(nmax);
//Deletes empty columns from the where statements appear matrix;
for(decl j=J;j>nmax-1;j--){pairapp=dropc(pairapp,j);}
println("Triplet item numbers in which the statement appears:");
print( "%c", {"Statement", "  Pairs in which statement appearance"}, "%cf",{"%8.4g", "%8.4g"}, range(1, S, 1)'~pairapp+1);

//Second error check: If pairs are updated together, then it assumes no statement repetition.;
	//So, if nappear is larger than 1, error end close;
if(nmax>1){println("ERROR, a statement appears more than once in the pairmap, and pairupdate was set to 1"); exit(1);}
}

//Read in the statement specifications for the quads;
if(choice==2){
decl tempspec;
decl mapfile=fopen(pairmap);
fscan(mapfile,"%#M",J,5,&tempspec);
fclose(mapfile);
pairspec=tempspec[][1:4];
	//Recode, because index in Ox begins at position 0, rather than 1;
pairspec=pairspec-1;

//Output statement pairings;
println("Quad Statements");
print( "%c", {"Item", "A", "B", "C", "D"}, "%cf",{"%8.4g", "%8.4g", "%8.4g", "%8.4g", "%8.4g"}, range(1, J, 1)'~pairspec+1);


//Specify which item pairs each statement appears in;
pairapp=constant(.NaN,S,J);
for(decl s=0;s<S;s++){
	decl col=0;
	for(decl j=0;j<J;j++){
	if(pairspec[j][0]==s||pairspec[j][1]==s||pairspec[j][2]==s||pairspec[j][3]==s){pairapp[s][col]=j;col=col+1;}
	}
}
//Counts how many items a statement appears in;
nappear=sumr(countr(pairapp,<0>));
println("Number of times each statement appears in a quad");
print( "%c", {"Statement", "  #appear"}, "%cf",{"%8.4g", "%8.4g"}, range(1, S, 1)'~nappear);

//Determines maximum number of times a statement appears;
nmax=max(nappear);
println("Maximum number of pairs in which a statement appears");
println(nmax);
//Deletes empty columns from the where statements appear matrix;
for(decl j=J;j>nmax-1;j--){pairapp=dropc(pairapp,j);}
println("Quad item numbers in which the statement appears:");
print( "%c", {"Statement", "  Pairs in which statement appearance"}, "%cf",{"%8.4g", "%8.4g"}, range(1, S, 1)'~pairapp+1);

//Second error check: If pairs are updated together, then it assumes no statement repetition.;
	//So, if nappear is larger than 1, error end close;
if(nmax>1){println("ERROR, a statement appears more than once in the pairmap, and pairupdate was set to 1"); exit(1);}
}


//Read in the Theta dimension specifications for statements;
decl tmpspec;
decl thsfile=fopen(thetaspec);
fscan(thsfile,"%#M",S,2,&tmpspec);
fclose(thsfile);
thspec=tmpspec[][1];
	//Recode, because index in Ox begins at position 0, rather than 1;
thspec=thspec-1;

//Output statement dimesionality;
//println("Statement Dimensions");
//print( "%c", {"Statement", "  Dimension"}, "%cf",{"%8.4g", "%8.4g"}, range(1, S, 1)'~thspec+1);




//Matrices to store the state of each chain (elements set to zero) during sampling;
decl mnstate=zeros(chains,D);
decl varstate=zeros(chains,D);
decl thcovstate=zeros((D*(D-1))/2,chains);
decl thstate=zeros(N,D*chains);
decl astate=zeros(S,chains);
decl dstate=zeros(S,chains);
decl tstate=zeros(S,chains);

//Matrices to store complete run of chains;
decl alphastates=zeros(S*chains,it);
decl deltastates=zeros(S*chains,it);
decl taustates=zeros(S*chains,it);

//Matrices & variables to store a running sum for each chain (elements set to zero);
decl smnchains=zeros(chains,D);
decl svarchains=zeros(chains,D);
decl scovchains=zeros((D*(D-1))/2,chains);
decl sthchains=zeros(N,D*chains);
decl sachains=zeros(S,chains);
decl sdchains=zeros(S,chains);
decl stchains=zeros(S,chains);
decl smnchains2=zeros(chains,D);
decl svarchains2=zeros(chains,D);
decl scovchains2=zeros((D*(D-1))/2,chains);
decl sthchains2=zeros(N,D*chains);
decl sachains2=zeros(S,chains);
decl sdchains2=zeros(S,chains);
decl stchains2=zeros(S,chains);
decl sthsum=zeros(N,D);
decl sthsum2=zeros(N,D);
decl smnsum,smnsum2;
decl svarsum,svarsum2;
decl sthcovsum,sthcovsum2;
decl sasum,sdsum,stsum;
decl sasum2,sdsum2,stsum2;
//Acceptance rate placeholder size differs based on estimation strategy.
	
//For block-level estimation, each item block has an acceptance rate;
acptalpha=zeros(J,1);acptdelta=zeros(J,1);acpttau=zeros(J,1);
acpttheta=zeros(N,1);acptthcov=0;acptmn=0;

//-------- Statement Priors -Only if EstPar=1 --------;

if(EstPar==1){
//Read in 4 parameter beta priors for Alpha parameters;
decl Alphapfile=fopen(AlphaPriorFile);
fscan(Alphapfile,"%#M",S,5,&apriors);
fclose(Alphapfile);
//Put into appropriate vectors;
Alphaa=apriors[][1];
Alphab=apriors[][2];
Alphamin=apriors[][3];
Alphamax=apriors[][4];

//Output Alpha priors to screeen;
//println("Alpha priors");
//print( "%c", {"Statement", "Shape a", "Shape b", "Min val", "Max val"}, "%cf",{"%8.4g", "%8.4g", "%8.4g", "%8.4g", "%8.4g"}, range(1, S, 1)'~Alphaa~Alphab~Alphamin~Alphamax);

//Read in 4 parameter beta priors for Delta parameters;
decl Deltapfile=fopen(DeltaPriorFile);
fscan(Deltapfile,"%#M",S,5,&dpriors);
fclose(Deltapfile);
//Put into appropriate vectors;
Deltaa=dpriors[][1];
Deltab=dpriors[][2];
Deltamin=dpriors[][3];
Deltamax=dpriors[][4];

//Output Delta priors to screeen;
//println("Delta priors");
//print( "%c", {"Statement", "Shape a", "Shape b", "Min val", "Max val"}, "%cf",{"%8.4g", "%8.4g", "%8.4g", "%8.4g", "%8.4g"}, range(1, S, 1)'~Deltaa~Deltab~Deltamin~Deltamax);

//Read in 4 parameter beta priors for Tau parameters;
decl Taupfile=fopen(TauPriorFile);
fscan(Taupfile,"%#M",S,5,&tpriors);
fclose(Taupfile);
//Put into appropriate vectors;
Taua=tpriors[][1];
Taub=tpriors[][2];
Taumin=tpriors[][3];
Taumax=tpriors[][4];

//Output Tau priors to screeen;
//println("Tau priors");
//print( "%c", {"Statement", "Shape a", "Shape b", "Min val", "Max val"}, "%cf",{"%8.4g", "%8.4g", "%8.4g", "%8.4g", "%8.4g"}, range(1, S, 1)'~Taua~Taub~Taumin~Taumax);

} //End EstPar=1 If;


//Initiate state 0 for each variable & chain;
for(decl c=0;c<chains;c++){
	//Obtain initial values for each variable from the function;
	initiate(c);
	mnstate[c][]=mn0;
	varstate[c][]=thvar0;
	thcovstate[][c]=thcov0;
	thstate[][c*D:c*D+(D-1)]=theta0;
	astate[][c]=alpha0;
	dstate[][c]=delta0;
	tstate[][c]=tau0;
}

//Variables to track iterations and flag whether to continue;
decl Cont=1;
decl i=0;

//Begin iterations for the chains;
while(Cont==1) {
	//To provide feedback during update: Print every Counter update;
	if(imod(i+1,Counter)==0) println("Beginning iteration ", i+1, ". Lapsed time so far: ", timespan(time0));
	for(decl c=0;c<chains;c++){
		//Set the temporary vectors to the current state of the chain;
		mn0=mnstate[c][];
		thcov0=thcovstate[][c];
		theta0=thstate[][c*D:c*D+(D-1)];
		alpha0=astate[][c];
		delta0=dstate[][c];
		tau0=tstate[][c];
		
		//Now draw & update;
		if(choice==0){ drawtheta1(); }
		if(choice==1){ drawtheta2(); }
		if(choice==2){ drawtheta3(); }
		if(EstPar==1){
			if(choice==0){ drawbeta1(); }
			if(choice==1){ drawbeta2(); }
			if(choice==2){ drawbeta3(); }
		} //If user has selected to estimate statement parameters, draw parameters;
		drawlamda();
		if(i>burn-1){  //Note: v4 removed call to update function, updates here;
			smnchains[c][]=smnchains[c][]+mn0;
			smnchains2[c][]=smnchains2[c][]+mn0.^2;
			svarchains[c][]=svarchains[c][]+thvar0;
			svarchains2[c][]=svarchains2[c][]+thvar0.^2;
			scovchains[][c]=scovchains[][c]+thcov0;
			scovchains2[][c]=scovchains2[][c]+thcov0.^2;
			sthchains[][c*D:c*D+(D-1)]=sthchains[][c*D:c*D+(D-1)]+theta0;
			sthchains2[][c*D:c*D+(D-1)]=sthchains2[][c*D:c*D+(D-1)]+theta0.^2;
			sachains[][c]=sachains[][c]+alpha0;
			sachains2[][c]=sachains2[][c]+alpha0.^2;
			sdchains[][c]=sdchains[][c]+delta0;
			sdchains2[][c]=sdchains2[][c]+delta0.^2;
			stchains[][c]=stchains[][c]+tau0;
			stchains2[][c]=stchains2[][c]+tau0.^2;
		}
		
		//Now, save the current state for the chain for next cycle;
		mnstate[c][]=mn0;
		varstate[c][]=thvar0;
		thcovstate[][c]=thcov0;
		thstate[][c*D:c*D+(D-1)]=theta0;
		astate[][c]=alpha0;
		dstate[][c]=delta0;
		tstate[][c]=tau0;

		//Save state of chain for all iterations in full matrix for later use;
		alphastates[c*S:c*S+(S-1)][i]=alpha0;
		deltastates[c*S:c*S+(S-1)][i]=delta0;
		taustates[c*S:c*S+(S-1)][i]=tau0;		
	} //End chain, update the next chain;
		
	//Functions to determine if updating should continue;
	i=i+1;
	if(i==it) Cont=0;
	time1=timer();
//	if(time1-time0>maxmins*100*60) Cont=0;
} //End iteration loop;

//------ Sum across the chains, for calculating mean & SD across chains-----
//Statement parameters
sasum=sumr(sachains);
sasum2=sumr(sachains2);
sdsum=sumr(sdchains);
sdsum2=sumr(sdchains2);
stsum=sumr(stchains);
stsum2=sumr(stchains2);

//Population parameters
smnsum=sumc(smnchains);
smnsum2=sumc(smnchains2);
svarsum=sumc(svarchains);
svarsum2=sumc(svarchains2);
sthcovsum=sumr(scovchains);
sthcovsum2=sumr(scovchains2);


//=============== Output results to screen =============================
println("------ Results  ------");
for(decl c=0;c<chains;c++){
	if(EstPar==1){ //If user selected to estimate statement parameters;
		//println("Chain ", c+1, " Parameter Means:");
		//print((sachains[][c]~sdchains[][c]~stchains[][c])/(i-burn));
	}
	//println("Chain ", c+1, " Population-Person Means:");
	//print((smnchains[c][])/(i-burn));
	//println("Chain ", c+1, " Population-Person Mean SDs:");
	//print(sqrt(((smnchains2[c][])-((smnchains[c][]).^2)/(i-burn))/(i-burn)));

	//Create the variance-covariance matrix for that replication for printing
	decl finalvar=(svarchains[c][])/(i-burn);
	decl finalcov=(scovchains[][c])/(i-burn);
	decl tmpcov=zeros(D,D);
	decl place=0; //counter variable;
	for(decl d=0;d<D;d++){
		tmpcov[d][d]=finalvar[d];
		for(decl dd=d+1;dd<D;dd++){
			tmpcov[d][dd]=finalcov[place];
			tmpcov[dd][d]=finalcov[place];
			place=place+1;
		}
	}
	//println("Chain ", c+1, " Theta Variance-Covariance Matrix:");
	//print(tmpcov);

	//Create the variance-covariance SD matrix for that replication for printing
	decl finalvar2=(svarchains2[c][])/(i-burn);
	decl finalcov2=(scovchains2[][c])/(i-burn);
	decl tmpcov2=zeros(D,D);
	place=0; //counter variable;
	for(decl d=0;d<D;d++){
		tmpcov2[d][d]=finalvar2[d];
		for(decl dd=d+1;dd<D;dd++){
			tmpcov2[d][dd]=finalcov2[place];
			tmpcov2[dd][d]=finalcov2[place];
			place=place+1;
		}
	}
	//println("Chain ", c+1, " Variance-Covariance SDs:");
	//print(tmpcov2);
}

decl parmeans, parSDs;
if(EstPar==1){ //If user selected to estimate statement parameters;
	//println("------ Means for each parameter ------");
	//println("== Alphas ==");
	//println(sachains/(i-burn));
	//println("== Deltas ==");
	//println(sdchains/(i-burn));
	//println("== Taus ==");
	//println(stchains/(i-burn));

	//println("------ Parameter means across chains  ------");
	//println("Alpha / Beta / Tau Parameters:");
	parmeans=(sasum~sdsum~stsum)/((i-burn)*chains);
	//println(parmeans);
	//println("------ Parameter standard deviations across chains ------");
	parSDs=sqrt(((sasum2~sdsum2~stsum2)-((sasum~sdsum~stsum).^2)/((i-burn)*chains))/((i-burn)*chains));
	//println(parSDs);
}
/////////////////////////////////////////////////////accuracy stats for item parameters: ABS, RMSE, CORR, PSD
decl genpar;
decl pfile=fopen(pars);
fscan(pfile,"%#M",S,3,&genpar);
fclose(pfile);

decl inits;
	decl initfile=fopen(parinits);
	fscan(initfile,"%#M",S,3,&inits);
	
decl sspar=zeros(S,3);
     sspar[0:S-1][0:2]=inits[0:S-1][0:2];

//println("------ Bias of Estimated Parameters ------");
decl bias=sspar-genpar;
for(decl j=0;j<S;j++){
	for(decl k=0;k<3;k++){
		if(bias[j][k]<0) bias[j][k]=-bias[j][k];
		else bias[j][k]=bias[j][k];
	}
}
//print(bias);
println("------ Overall Bias of Estimated Parameters ------");
print(sumc(bias)/S);

decl corr=correlation(genpar~sspar);
println("------- Correlation Between True and Estimated parameters --------");
println(corr);

decl RMSEpart1 = bias.^2;
decl RMSE = sqrt(sumc(RMSEpart1)/S);
print("\n","-------   Root Mean Square Errors (RMSE)   ------","\n");
print(RMSE,"\n");

//decl parM, PSD;
//parM=sumc(parmeans)/S;
//	PSD=sqrt(sumc((parmeans-parM).^2)/S);
//println("------ posterior standard deviations (PSDs) ------");
//println(sumc(parSDs)/S);

/////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////accuracy stats for thetas: ABS, RMSE, CORR, PSD
// Calculate the sum of the values across chains;
decl sumth=zeros(N,D);
decl sumth2=zeros(N,D);
for(decl d=0;d<D;d++){
	for(decl c=0;c<chains;c++){
		sumth[][d]=sumth[][d]+sthchains[][c*D+d];
		sumth2[][d]=sumth2[][d]+sthchains2[][c*D+d];
	}
}
decl thmeans = sumth/((i-burn)*chains);

decl gentheta;
decl thfile=fopen(theta_file);
fscan(thfile,"%#M",N,D,& gentheta);
fclose(thfile);

//println("------ Bias of Estimated thetas ------");
decl biastheta=thmeans-gentheta;
for(decl t=0;t<N;t++){
	for(decl k=0;k<D;k++){
		if(biastheta[t][k]<0) biastheta[t][k]=-biastheta[t][k];
		else biastheta[t][k]=biastheta[t][k];
	}
}
//print(biastheta);
println("------ Overall Bias of Estimated thetas ------");
print(sumc(biastheta)/N);

decl corrtheta=correlation(gentheta~thmeans);
println("------- Correlation Between True and Estimated thetas --------");
println(corrtheta);

decl RMSEthetapart1 = biastheta.^2;
decl RMSEtheta = sqrt(sumc(RMSEthetapart1)/N);
print("\n","-------   Root Mean Square Errors for thetas (RMSE)   ------","\n");
print(RMSEtheta,"\n");

//decl parMtheta, PSDtheta;
//parMtheta=sumc(thmeans)/N;
//	PSDtheta=sqrt(sumc((thmeans-parMtheta).^2)/N);
decl thSDs=sqrt((sumth2-(sumth.^2)/((i-burn)*chains))/((i-burn)*chains));
println("------ posterior standard deviations for thetas (PSDs) ------");
println(sumc(thSDs)/N);


//println("------ Population Means: Means across chains  ------");
decl popmeans=(smnsum)/((i-burn)*chains);
//println(popmeans);
//println("------ Population Means: Standard deviations across chains ------");
decl popSDs=sqrt(((smnsum2)-((smnsum).^2)/((i-burn)*chains))/((i-burn)*chains));
//println(popSDs);

//println("------ Population Variance-Covariance Matrix: Means across chains  ------");
decl covmeans=(sthcovsum)/((i-burn)*chains);
decl varmeans=(svarsum)/((i-burn)*chains);
//Construct the covariance matrix for output;
decl popcov=zeros(D,D);
decl place=0; //counter variable;
for(decl d=0;d<D;d++){
	popcov[d][d]=varmeans[d];
	for(decl dd=d+1;dd<D;dd++){
		popcov[d][dd]=covmeans[place];
		popcov[dd][d]=covmeans[place];
		place=place+1;
	}
}
//print(popcov);
/////////////////////////////////////////////////////////////////////////////////////////////////////////


//println("------ Population Variance-Covariance Matrix: Standard deviations across chains ------");
decl covSDs=sqrt(((sthcovsum2)-((sthcovsum).^2)/((i-burn)*chains))/((i-burn)*chains));
decl varSDs=sqrt(((svarsum2)-((svarsum).^2)/((i-burn)*chains))/((i-burn)*chains));
decl popcovSD=zeros(D,D);
place=0; //counter variable;
for(decl d=0;d<D;d++){
	popcovSD[d][d]=varSDs[d];
	for(decl dd=d+1;dd<D;dd++){
		popcovSD[d][dd]=covSDs[place];
		popcovSD[dd][d]=covSDs[place];
		place=place+1;
	}
}
//print(popcovSD);


// Calculate the sum of the values across chains;
//decl sumth=zeros(N,D);
//decl sumth2=zeros(N,D);
//for(decl d=0;d<D;d++){
//	for(decl c=0;c<chains;c++){
//		sumth[][d]=sumth[][d]+sthchains[][c*D+d];
//		sumth2[][d]=sumth2[][d]+sthchains2[][c*D+d];
//	}
//}
//decl thmeans = sumth/((i-burn)*chains);
////////////////////Model Fit Statistics////////////////////
decl finala = alpha0;
decl finald = delta0;
decl finalt = tau0;
if(choice==0) {
	decl LL = sumr(sumc(Likelihood1(finala,finald,finalt,thmeans,thspec,pairspec,J,X)));
	decl npar = 3*S;
	decl AIC = -2*LL+npar;
	decl BIC = -2*LL+npar*log(N);
	print("\n","-------        Model Fit Statistics        ------");
	print("\n","-------(Appxominations Based on Posterior Means)------","\n");
	print("%r",{" log-Likelihood    "," Deviance    "," AIC    "," BIC    "},"%10.4f", LL|-2*LL|AIC|BIC);
	print("\n");
	}
if(choice==1) {
	decl LL = sumr(sumc(Likelihood2(finala,finald,finalt,thmeans,thspec,pairspec,J,X)));
	decl npar = 3*S;
	decl AIC = -2*LL+npar;
	decl BIC = -2*LL+npar*log(N);
	print("\n","-------        Model Fit Statistics        ------");
	print("\n","-------(Appxominations Based on Posterior Means)------","\n");
	print("%r",{" log-Likelihood    "," Deviance    "," AIC    "," BIC    "},"%10.4f", LL|-2*LL|AIC|BIC);
	print("\n");
	}
if(choice==2) {
	decl LL = sumr(sumc(Likelihood3(finala,finald,finalt,thmeans,thspec,pairspec,J,X)));
	decl npar = 3*S;
	decl AIC = -2*LL+npar;
	decl BIC = -2*LL+npar*log(N);
	print("\n","-------        Model Fit Statistics        ------");
	print("\n","-------(Appxominations Based on Posterior Means)------","\n");
	print("%r",{" log-Likelihood    "," Deviance    "," AIC    "," BIC    "},"%10.4f", LL|-2*LL|AIC|BIC);
	print("\n");
	}

//////////////////// Calculate R statistics (Gelman & Runbin,1992) //////////////////

decl Ba=zeros(S,chains);
decl Bd=zeros(S,chains);
decl Bt=zeros(S,chains);

for (decl c=0;c<chains;c++){
	Ba[][c]= ((sachains[][c]/(i-burn))-(sasum/((i-burn)*chains))).^2;
	Bd[][c]= ((sdchains[][c]/(i-burn))-(sdsum/((i-burn)*chains))).^2;
	Bt[][c]= ((stchains[][c]/(i-burn))-(stsum/((i-burn)*chains))).^2;

	}
decl Balpha=sumr(Ba)/(chains-1);
decl Bdelta=sumr(Bd)/(chains-1);
decl Btau=sumr(Bt)/(chains-1);

decl Wa=zeros(S*chains,it-burn);
decl Wd=zeros(S*chains,it-burn);
decl Wt=zeros(S*chains,it-burn);

for (decl c=0;c<chains;c++){
	for (decl t=0;t<i-burn;t++){	
		Wa[c*S:c*S+(S-1)][t]=(alphastates[c*S:c*S+(S-1)][burn+t]-sachains[][c]/(i-burn)).^2;
		Wd[c*S:c*S+(S-1)][t]=(deltastates[c*S:c*S+(S-1)][burn+t]-sdchains[][c]/(i-burn)).^2;
		Wt[c*S:c*S+(S-1)][t]=(taustates[c*S:c*S+(S-1)][burn+t]-stchains[][c]/(i-burn)).^2;

	}
}
decl Waa=sumr(Wa);
decl Wdd=sumr(Wd);
decl Wtt=sumr(Wt);

decl Waaa=zeros(S,chains);
decl Wddd=zeros(S,chains);
decl Wttt=zeros(S,chains);

for (decl c=0;c<chains;c++){
	Waaa[][c]=Waa[c*S:c*S+(S-1)];
	Wddd[][c]=Wdd[c*S:c*S+(S-1)];
	Wttt[][c]=Wtt[c*S:c*S+(S-1)];	
	}
	
decl Walpha=sumr(Waaa)/((i-burn)*chains);
decl Wdelta=sumr(Wddd)/((i-burn)*chains);
decl Wtau=sumr(Wttt)/((i-burn)*chains);

decl Salpha=(i-burn-1)/(i-burn).*Walpha+Balpha;
decl Sdelta=(i-burn-1)/(i-burn).*Wdelta+Bdelta;
decl Stau=(i-burn-1)/(i-burn).*Wtau+Btau;

decl Ralpha=((chains+1)/chains).*Salpha./Walpha-((i-burn-1)/(chains*(i-burn)));
decl Rdelta=((chains+1)/chains).*Sdelta./Wdelta-((i-burn-1)/(chains*(i-burn)));
decl Rtau=((chains+1)/chains).*Stau./Wtau-((i-burn-1)/(chains*(i-burn)));


println("------ Convergence Criterion: R statistics < 1.2 ------");
println("Alpha / Beta / Tau Parameters:");
println(Ralpha~Rdelta~Rtau);


println("------ Acceptance Rates  ------");
if(EstPar==1){ //If user selected to estimate statement parameters;
	println("Parameters:");
	println((acptalpha~acptdelta~acpttau)/(i*chains));
}
println("Means:");
println(acptmn/(i*chains));
println("Covariances:");
println(acptthcov/(i*chains));
println("Average theta:");
println(sumc(acpttheta/(i*chains))/N);

decl np=0;
for (decl q=0; q<S; q++){
if (Ralpha[q]>=1.2){
np=np+1;
}
}
for (decl p=0; p<S; p++){
if (Rdelta[p]>=1.2){
np=np+1;
}
}
for (decl m=0; m<S; m++){
if (Rtau[m]>=1.2){
np=np+1;
}
}
decl CR=100*np/(S*3);
println("------ Convergence Rate ------");
println(100-CR);

decl npa=0;
for (decl q=0; q<S; q++){
if (Ralpha[q]>=1.2){
npa=npa+1;
}
}

decl CRa=100*npa/S;
println("------Alpha Convergence Rate ------");
println(100-CRa);

decl npd=0;
for (decl q=0; q<S; q++){
if (Rdelta[q]>=1.2){
npd=npd+1;
}
}

decl CRd=100*npd/S;
println("------Delta Convergence Rate ------");
println(100-CRd);

decl npt=0;
for (decl q=0; q<S; q++){
if (Rtau[q]>=1.2){
npt=npt+1;
}
}

decl CRt=100*npt/S;
println("------Tau Convergence Rate ------");
println(100-CRt);

println("Lapsed time: ", timespan(time0));


//============= Output results to file, if options selected =================
//--- Output statement estimates to file, if option selected
if(outputparresults==1){
	format(252);
	decl outres=sprint(parresultfile);
	decl fileres=fopen(outres,"w");
	//fprint(fileres,parmeans);
	fprint(fileres,"%#M",parmeans);
	fclose(fileres);
}

//--- Output population estimates to file, if option selected
if(outputpopresults==1){
	format(252);
	decl outpopres=sprint(popresultfile);
	decl filepopres=fopen(outpopres,"w");
	fprintln(filepopres,"Population Means:");
	fprint(filepopres,"%#M",popmeans);
	fprintln(filepopres,"Population Means SDs:");
	fprint(filepopres,"%#M",popSDs);
	fprintln(filepopres,"Population Variance-covariance matrix:");
	fprint(filepopres,"%#M",popcov);
	fprintln(filepopres,"Population Variance-covariance SD matrix:");
	fprint(filepopres,"%#M",popcovSD);
	fclose(filepopres);
}

//--- Output thetas to file, if option selected;
if(outputtheta==1){
	// Calculate the sum of the values across chains;
	decl sumth=zeros(N,D);
	decl sumth2=zeros(N,D);
	for(decl d=0;d<D;d++){
		for(decl c=0;c<chains;c++){
			sumth[][d]=sumth[][d]+sthchains[][c*D+d];
			sumth2[][d]=sumth2[][d]+sthchains2[][c*D+d];
		}
	}
	format(252);
	decl outth=sprint(thetafile);
	decl fileth=fopen(outth,"w");
	//fprintln(fileth," ");
	fprint(fileth,"%#M",sumth/((i-burn)*chains));
//	fprintln(fileth,"Theta SDs:");
//	fprint(fileth,"%#M",sqrt((sumth2-(sumth.^2)/((i-burn)*chains))/((i-burn)*chains)));
	fclose(fileth);
}

}//End main program