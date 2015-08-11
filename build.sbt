organization := "net.proofpeer"

name := "ProofPeer ProofScript"

version := "0.2"

scalaVersion := "2.11.6"

scalacOptions += "-feature"

scalacOptions += "-deprecation"

libraryDependencies += "net.proofpeer" %% "proofpeer-general" % "0.1-SNAPSHOT"

libraryDependencies += "net.proofpeer" %% "proofpeer-indent" % "0.5-SNAPSHOT"

libraryDependencies += "net.proofpeer" %% "metis" % "0.2-SNAPSHOT"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"

libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.1.1"
