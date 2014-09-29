organization := "net.proofpeer"

name := "ProofPeer ProofScript"

version := "0.1"

scalaVersion := "2.11.1"

scalacOptions += "-feature"

libraryDependencies += "net.proofpeer" %% "proofpeer-scala" % "0.2-SNAPSHOT"

libraryDependencies += "net.proofpeer" %% "proofpeer-indent" % "0.3-SNAPSHOT"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"
