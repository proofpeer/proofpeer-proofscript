organization := "net.proofpeer"

name := "ProofPeer ProofScript"

version := "0.2-SNAPSHOT"

scalaVersion := "2.11.2"

scalacOptions += "-feature"

libraryDependencies += "net.proofpeer" %% "proofpeer-general" % "0.1-SNAPSHOT"

libraryDependencies += "net.proofpeer" %% "proofpeer-indent" % "0.4-SNAPSHOT"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"
