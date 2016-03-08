lazy val root = project.in(file(".")).aggregate(proofscriptJS, proofscriptJVM).
  settings(
    publish := {},
    publishLocal := {}
  )

lazy val proofscript = crossProject.in(file(".")).
  settings(
    name := "ProofPeer ProofScript",
    organization := "net.proofpeer",
    version := "0.3-SNAPSHOT",
    scalaVersion := "2.11.7",
    scalacOptions += "-feature",
    scalacOptions += "-deprecation",
    libraryDependencies += "net.proofpeer" %%% "proofpeer-general" % "0.1-SNAPSHOT",
    libraryDependencies += "net.proofpeer" %%% "proofpeer-indent" % "0.5-SNAPSHOT",
    libraryDependencies += "net.proofpeer" %%% "metis" % "0.2-SNAPSHOT",
    libraryDependencies += "net.proofpeer" %%% "proofpeer-versionary" % "0.1-SNAPSHOT"    
  ).
  jvmSettings(
    libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.3",
    libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"
  ).
  jsSettings(
    libraryDependencies += "com.github.japgolly.fork.scalaz" %%% "scalaz-core" % "7.1.3"
  )

lazy val proofscriptJS = proofscript.js
lazy val proofscriptJVM = proofscript.jvm
