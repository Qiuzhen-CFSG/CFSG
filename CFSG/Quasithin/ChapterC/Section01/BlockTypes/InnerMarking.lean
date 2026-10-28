module
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
/-!
# Inner markings of actual block modules

Simultaneously conjugating the marked quotient by an actor and applying
that actor to the module preserves the exact intertwining identity. This
allows a Sylow quotient to be placed in standard coordinates without
changing either the prescribed natural representation or the original group.
-/
public section
namespace CFSG.Quasithin.ChapterC.BlockModuleModel
variable {L A V : Type*} [Group L] [Group A] [Group V]

/-- Inner relabelling of the actor preserves the actual conjugation module. -/
@[expose] def innerMarking {rho : A →* MulAut V}
    (model : BlockModuleModel L rho) (a : A) : BlockModuleModel L rho where
  quotientIso := model.quotientIso.trans (MulAut.conj a)
  moduleIso := model.moduleIso.trans (rho a)
  intertwining l u := by
    change rho a (model.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u))) =
      rho ((MulAut.conj a) (model.quotientIso (QuotientGroup.mk' (pCore 2 L) l)))
        (rho a (model.moduleIso (QuotientGroup.mk' (blockFixed L) u)))
    rw [model.intertwining]
    have he (b : A) : rho a * rho b = rho (MulAut.conj a b) * rho a := by
      simp only [MulAut.conj_apply, map_mul, map_inv]
      group
    exact congrArg (fun f : MulAut V => f (model.moduleIso (QuotientGroup.mk' (blockFixed L) u)))
      (he (model.quotientIso (QuotientGroup.mk' (pCore 2 L) l)))
end CFSG.Quasithin.ChapterC.BlockModuleModel
