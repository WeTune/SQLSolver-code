create table Student (
        StuID        INTEGER PRIMARY KEY,
        LName        VARCHAR(12),
        Fname        VARCHAR(12),
        Age      INTEGER,
        Sex      VARCHAR(1),
        Major        INTEGER,
        Advisor      INTEGER,
        city_code    VARCHAR(3)
 );

create table Video_Games (
       GameID           INTEGER PRIMARY KEY,
       GName            VARCHAR(40),
       GType            VARCHAR(40)
);

create table Plays_Games (
       StuID                INTEGER,
       GameID            INTEGER,
       Hours_Played      INTEGER,
       FOREIGN KEY(GameID) REFERENCES Video_Games(GameID),
       FOREIGN KEY(StuID) REFERENCES Student(StuID)
);

create table SportsInfo (
  StuID INTEGER,
  SportName VARCHAR(32),
  HoursPerWeek INTEGER,
  GamesPlayed INTEGER,
  OnScholarship VARCHAR(1),
  FOREIGN KEY(StuID) REFERENCES Student(StuID)
);


insert into Student values ( 1001, 'Smith', 'Linda', 18, 'F', 600, 1121,'BAL');
 insert into Student values ( 1002, 'Kim', 'Tracy', 19, 'F', 600, 7712,'HKG');
 insert into Student values ( 1003, 'Jones', 'Shiela', 21, 'F', 600, 7792,'WAS');
 insert into Student values ( 1004, 'Kumar', 'Dinesh', 20, 'M', 600, 8423,'CHI');
 insert into Student values ( 1005, 'Gompers', 'Paul', 26, 'M', 600, 1121,'YYZ');
 insert into Student values ( 1006, 'Schultz', 'Andy', 18, 'M', 600, 1148,'BAL');
 insert into Student values ( 1007, 'Apap', 'Lisa', 18, 'F', 600, 8918,'PIT');
 insert into Student values ( 1008, 'Nelson', 'Jandy', 20, 'F', 600, 9172,'BAL');
 insert into Student values ( 1009, 'Tai', 'Eric', 19, 'M', 600, 2192,'YYZ');
 insert into Student values ( 1010, 'Lee', 'Derek', 17, 'M', 600, 2192,'HOU');
 insert into Student values ( 1011, 'Adams', 'David', 22, 'M', 600, 1148,'PHL');
 insert into Student values ( 1012, 'Davis', 'Steven', 20, 'M', 600, 7723,'PIT');
 insert into Student values ( 1014, 'Norris', 'Charles', 18, 'M', 600, 8741, 'DAL');
 insert into Student values ( 1015, 'Lee', 'Susan', 16, 'F', 600, 8721,'HKG');
 insert into Student values ( 1016, 'Schwartz', 'Mark', 17, 'M', 600, 2192,'DET');
 insert into Student values ( 1017, 'Wilson', 'Bruce', 27, 'M', 600, 1148,'LON');
 insert into Student values ( 1018, 'Leighton', 'Michael', 20, 'M', 600, 1121, 'PIT');
 insert into Student values ( 1019, 'Pang', 'Arthur', 18, 'M', 600, 2192,'WAS');
 insert into Student values ( 1020, 'Thornton', 'Ian', 22, 'M', 520, 7271,'NYC');
 insert into Student values ( 1021, 'Andreou', 'George', 19, 'M', 520, 8722, 'NYC');
 insert into Student values ( 1022, 'Woods', 'Michael', 17, 'M', 540, 8722,'PHL');
 insert into Student values ( 1023, 'Shieber', 'David', 20, 'M', 520, 8722,'NYC');
 insert into Student values ( 1024, 'Prater', 'Stacy', 18, 'F', 540, 7271,'BAL');
 insert into Student values ( 1025, 'Goldman', 'Mark', 18, 'M', 520, 7134,'PIT');
 insert into Student values ( 1026, 'Pang', 'Eric', 19, 'M', 520, 7134,'HKG');
 insert into Student values ( 1027, 'Brody', 'Paul', 18, 'M', 520, 8723,'LOS');
 insert into Student values ( 1028, 'Rugh', 'Eric', 20, 'M', 550, 2311,'ROC');
 insert into Student values ( 1029, 'Han', 'Jun', 17, 'M', 100, 2311,'PEK');
 insert into Student values ( 1030, 'Cheng', 'Lisa', 21, 'F', 550, 2311,'SFO');
 insert into Student values ( 1031, 'Smith', 'Sarah', 20, 'F', 550, 8772,'PHL');
 insert into Student values ( 1032, 'Brown', 'Eric', 20, 'M', 550, 8772,'ATL');
 insert into Student values ( 1033, 'Simms', 'William', 18, 'M', 550, 8772,'NAR');
 insert into Student values ( 1034, 'Epp', 'Eric', 18, 'M', 050, 5718,'BOS');
 insert into Student values ( 1035, 'Schmidt', 'Sarah', 26, 'F', 050, 5718,'WAS');

insert into Video_Games values ( 1, 'RNG Stone', 'Collectible card game');
insert into Video_Games values ( 2, 'The Vanishing of Eric Calder', 'Walking Simulator');
insert into Video_Games values ( 3, 'Grand Term Assignment', 'Role-playing game');
insert into Video_Games values ( 4, 'Europe is the Universe', 'Grand strategy');
insert into Video_Games values ( 5, 'Call of Destiny', 'Frist-person shooter');
insert into Video_Games values ( 6, 'Works of Widenius', 'Massively multiplayer online game');

insert into Plays_Games values ( 1001, 1, 35);
insert into Plays_Games values ( 1001, 2, 15);
insert into Plays_Games values ( 1001, 5, 1);
insert into Plays_Games values ( 1007, 4, 1000);
insert into Plays_Games values ( 1008, 5, 50);
insert into Plays_Games values ( 1008, 3, 50);
insert into Plays_Games values ( 1010, 6, 1337);
insert into Plays_Games values ( 1032, 1, 47);
insert into Plays_Games values ( 1032, 2, 10);
insert into Plays_Games values ( 1032, 3, 100);















