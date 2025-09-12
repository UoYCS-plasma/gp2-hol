open HolKernel

val () = new_theory "typing"


Datatype: ty = tyInt | tyChar | tyString | tyAtom | tyList
End

Definition is_direct_subtype_of_def:
  is_direct_subtype_of tyInt tyAtom = T /\
  is_direct_subtype_of tyChar tyString = T /\
  is_direct_subtype_of tyString tyAtom = T /\
  is_direct_subtype_of tyAtom tyList = T /\
  is_direct_subtype_of _ _ = F
End

Definition is_subtype_of_def:
  is_subtype_of = RTC is_direct_subtype_of
End


val () = export_theory ()
