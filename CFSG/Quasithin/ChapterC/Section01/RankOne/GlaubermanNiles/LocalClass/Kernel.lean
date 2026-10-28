module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.SmallField
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Elementary
public import Theory.GroupTheory.MinimalParabolicFrattiniKernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSetup

/-!
# The actual C.1.17 action kernel is a Frattini kernel

The derived subgroup of binary SL₂ embeds in the derived subgroup of every
characteristic-two PSL₂, so the marked actor is never a two-group, including
field order two. Thus the action kernel and a Sylow subgroup have proper
join. Unique maximality and the core-central module construction then put
the kernel image modulo O₂(H) in the Frattini subgroup. This proves the
literal no-partial-complement requirement in Campbell's rank-one setup.
The separate identification of the full action quotient with PSL₂ is not
assumed or asserted here.

Source: Aschbacher–Smith C.1.17, printed p.126; Campbell, *Pushing up in
Finite Groups* (1979), Hypothesis (E), printed p.9.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles

theorem derived_psl_not_isPGroup_two (F : Type) [Field F] [CharP F 2] :
    ¬ IsPGroup 2 (commutator PSL(2,F)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let i : ZMod 2 →+* F := ZMod.castHom (by simp) F
  let j : SL(2,ZMod 2) →* SL(2,F) := Matrix.SpecialLinearGroup.map i
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    ext x y
    apply i.injective
    exact congrArg (fun a : SL(2,F) => a.val x y) hab
  let g : SL(2,ZMod 2) →* PSL(2,F) :=
    Atlas.RankOneFieldAutomorphisms.slEquivPSL.toMonoidHom.comp j
  have hg : Function.Injective g :=
    Atlas.RankOneFieldAutomorphisms.slEquivPSL.injective.comp hj
  have hm : (commutator SL(2,ZMod 2)).map g ≤ commutator PSL(2,F) := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let f : commutator SL(2,ZMod 2) →* commutator PSL(2,F) :=
    (g.comp (commutator SL(2,ZMod 2)).subtype).codRestrict _
      (fun x => hm (mem_map_of_mem g x.property))
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (hg (congrArg Subtype.val he))
  intro hp
  have hh := (hp.of_injective f hf).card_eq_or_dvd
  rw [Stellmacher.isSL2Two_commutator_card ⟨MulEquiv.refl _⟩] at hh
  norm_num at hh

variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.localStar_not_isPGroup_two (h : InLocalClass e) : ¬ IsPGroup 2 (LocalStar e) := by
  intro hp
  obtain ⟨n,hn,F,_,_,_,hF,⟨m⟩⟩ := h.natural
  exact derived_psl_not_isPGroup_two F ((hp.to_subgroup (generalizedFitting (LocalStar e))).of_equiv m.actorIso)

theorem InLocalClass.kernel_sup_sylow_lt_top (h : InLocalClass e) (T : Sylow 2 H) :
    localKernel e ⊔ (T : Subgroup H) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  exact InLocalClass.localStar_not_isPGroup_two h (isPGroup_quotient_of_sup_eq_top (localKernel e) T T.isPGroup' he)

theorem InLocalClass.core_le_localKernel (h : InLocalClass e) : pCore 2 H ≤ localKernel e := by
  apply Subgroup.le_centralizer_iff.mpr
  intro x hx y hy
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp
    (h.localV_le_coreOmegaCenter hx)).2.2 y hy

/-- The original C.1.17 action kernel has Frattini image modulo the actual two-core. -/
theorem InLocalClass.kernel_image_le_frattini (h : InLocalClass e) :
    (localKernel e).map (QuotientGroup.mk' (pCore 2 H)) ≤ frattini (H ⧸ pCore 2 H) := by
  obtain ⟨T,_,hT⟩ := h.sylow
  exact normal_image_le_frattini_of_uniqueMaximal T hT.1 (localKernel e)
    h.core_le_localKernel (h.kernel_sup_sylow_lt_top T)

/-- The source action kernel satisfies Campbell's literal supplement condition;
no new hypothesis on supplements or on the quotient is required. -/
theorem InLocalClass.kernel_noPartialComplement (h : InLocalClass e) :
    Campbell.NoPartialComplement ((localKernel e).map (QuotientGroup.mk' (pCore 2 H))) := by
  intro U hU
  apply frattini_nongenerating
  apply top_unique
  rw [← hU]
  exact sup_le (h.kernel_image_le_frattini.trans le_sup_right) le_sup_left

end CFSG.Quasithin.ChapterC.GlaubermanNiles
