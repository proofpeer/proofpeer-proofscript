lazy val root = project.in(file(".")).aggregate(fooJS, fooJVM).
  settings(
    publish := {},
    publishLocal := {}
  )

lazy val foo = crossProject.in(file(".")).
  settings(
    name := "ProofPeer ProofScript",
    organization := "net.proofpeer",
    version := "0.3-SNAPSHOT",
    scalaVersion := "2.11.6",
    scalacOptions += "-feature",
    scalacOptions += "-deprecation",
    libraryDependencies += "net.proofpeer" %%% "proofpeer-general" % "0.1-SNAPSHOT",
    libraryDependencies += "net.proofpeer" %%% "proofpeer-indent" % "0.5-SNAPSHOT",
    libraryDependencies += "net.proofpeer" %%% "metis" % "0.2-SNAPSHOT"
  ).
  jvmSettings(
    libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.1",
    libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"
  ).
  jsSettings(
    libraryDependencies += "com.github.japgolly.fork.scalaz" %%% "scalaz-core" % "7.1.0-4"
  )

lazy val fooJS = foo.js
lazy val fooJVM = foo.jvm