signature ROSE_TREE =
sig
  structure Forest : SPINE
  datatype 'a t = NIL | @^ of 'a * 'a t forest
  withtype 'a forest = 'a Forest.t
end
