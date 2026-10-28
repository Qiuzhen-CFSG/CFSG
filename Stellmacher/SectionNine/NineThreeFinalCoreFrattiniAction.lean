module

public import Stellmacher.SectionNine.NineThreeFinalCoreHyperplaneSetup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# The actual Frattini/mixed-line core action in (9.3)

For a finite characteristic-two group C and a central exponent-two subgroup
R, conjugation on O₂(C)/(Φ(O₂(C))(R ∩ O₂(C))) has kernel exactly O₂(C).
Automorphisms fixing R pointwise and acting trivially modulo Φ(D)R have
squares in the Frattini automorphism kernel. Burnside's basis-kernel theorem
therefore makes their group a two-group. Characteristic two bounds the
kernel of the original action on D; the kernel/image extension argument
then identifies the full quotient-action kernel.

The final theorem constructs this action for the literal mixed subgroup
and ambient centralizer in (9.3), retaining the original embedding. It also
proves that its module is elementary abelian. It does not assume a natural
module, a displacement bound, or any odd-layer commutator containment.
The rank-three action implication remains a separate step.

Source: Stellmacher (9.3), printed p.50/PDF p.40, the final R₀,C₀ paragraph
of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem fixed_central_frattini_automorphisms_isPGroup
    {D : Type u} [Group D] [Finite D]
    (htwo : IsPGroup 2 D) (actors : Subgroup (MulAut D)) (line : Subgroup D)
    (hfixed : ∀ actor : actors, ∀ vector ∈ line, (actor : MulAut D) vector = vector)
    (hexponent : ∀ vector ∈ line, vector ^ 2 = 1)
    (hdisplacement : ∀ actor : actors, ∀ vector : D,
      vector⁻¹ * (actor : MulAut D) vector ∈ frattini D ⊔ line) :
    IsPGroup 2 actors := by
  let quotient := QuotientGroup.mk' (frattini D)
  have hsquare (actor : actors) :
      (actor.val ^ 2) ∈ (Subgroup.quotientAut (frattini D)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro vector
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective (frattini D) vector
    rw [Subgroup.quotientAut_apply_mk]
    change quotient ((actor.val ^ 2) original) = quotient original
    obtain ⟨frattiniVector, hfrattiniVector, lineVector, hlineVector, heq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (hdisplacement actor original)
    have hformula : actor.val original = original * frattiniVector * lineVector := by
      have hh := congrArg (fun value : D => original * value) heq
      simpa [mul_assoc] using hh.symm
    have hzero : quotient frattiniVector = 1 :=
      (QuotientGroup.eq_one_iff (N := frattini D) frattiniVector).mpr hfrattiniVector
    have hzeroActed : quotient (actor.val frattiniVector) = 1 := by
      apply (QuotientGroup.eq_one_iff (N := frattini D) _).mpr
      exact (Subgroup.characteristic_iff_map_le.mp inferInstance actor.val)
        (Subgroup.mem_map_of_mem _ hfrattiniVector)
    change quotient (actor.val (actor.val original)) = quotient original
    calc
      quotient (actor.val (actor.val original)) =
          quotient (actor.val original) * quotient (actor.val frattiniVector) *
            quotient (actor.val lineVector) := by
              conv_lhs => rw [hformula]
              simp only [map_mul]
      _ = quotient original * quotient lineVector * quotient lineVector := by
        rw [hzeroActed, hfixed actor lineVector hlineVector, hformula, map_mul,
          map_mul, hzero]
        simp
      _ = quotient original := by
        rw [mul_assoc, ← map_mul, ← pow_two, hexponent lineVector hlineVector, map_one,
          mul_one]
  intro actor
  obtain ⟨power, hpower⟩ := (Subgroup.isPGroup_quotientAut_frattini_kernel htwo)
    ⟨actor.val ^ 2, hsquare actor⟩
  refine ⟨power + 1, ?_⟩
  apply Subtype.ext
  have heq := congrArg (fun element : (Subgroup.quotientAut (frattini D)).ker =>
    (element : MulAut D)) hpower
  change (actor.val ^ 2) ^ (2 ^ power) = 1 at heq
  change actor.val ^ (2 ^ (power + 1)) = 1
  rw [pow_succ, Nat.mul_comm, pow_mul]
  exact heq

public theorem frattini_core_conjugation_kernel_eq
    {C : Type u} [Group C] [Finite C]
    (hcharacteristic : Subgroup.centralizer (pCore 2 C : Set C) ≤ pCore 2 C) :
    ((Subgroup.quotientAut (frattini (pCore 2 C))).comp
      (MulAut.conjNormal : C →* MulAut (pCore 2 C))).ker = pCore 2 C := by
  let _ : Fact (IsPGroup 2 (pCore 2 C)) := ⟨pCore_isPGroup⟩
  let conjugation : C →* MulAut (pCore 2 C) := MulAut.conjNormal
  have hker : conjugation.ker ≤ pCore 2 C := by
    intro actor hactor
    apply hcharacteristic
    apply Subgroup.mem_centralizer_iff.mpr
    intro vector hvector
    have heq := DFunLike.congr_fun (MonoidHom.mem_ker.mp hactor) ⟨vector, hvector⟩
    have hh := congrArg Subtype.val heq
    change actor * vector * actor⁻¹ = vector at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have htwo : IsPGroup 2 conjugation.ker := pCore_isPGroup.to_le hker
  have hpreimage := (Subgroup.isPGroup_quotientAut_frattini_kernel
    (pCore_isPGroup (p := 2) (G := C))).comap_of_ker_isPGroup conjugation htwo
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, hpreimage⟩
  · intro actor hactor
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro vector
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective (frattini (pCore 2 C)) vector
    rw [MonoidHom.comp_apply, Subgroup.quotientAut_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (⟨actor, hactor⟩ : pCore 2 C) * original *
      (⟨actor, hactor⟩ : pCore 2 C)⁻¹ / original ∈ frattini (pCore 2 C)
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      commutator_le_frattini_of_isPGroup (p := 2)
        (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top (⟨actor, hactor⟩ : pCore 2 C)) (Subgroup.mem_top original))

public theorem exists_core_frattini_central_action
    {C : Type u} [Group C] [Finite C]
    (hcharacteristic : Subgroup.centralizer (pCore 2 C : Set C) ≤ pCore 2 C)
    (line : Subgroup C) [line.Normal]
    (hcenter : line ≤ Subgroup.center C)
    (hexponent : ∀ vector ∈ line, vector ^ 2 = 1) :
    let layer := frattini (pCore 2 C) ⊔ line.subgroupOf (pCore 2 C)
    ∃ action : C →* MulAut ((pCore 2 C) ⧸ layer),
      (∀ actor : C, ∀ vector : pCore 2 C,
        action actor (QuotientGroup.mk' layer vector) =
          QuotientGroup.mk' layer (MulAut.conjNormal actor vector)) ∧
      action.ker = pCore 2 C := by
  let core := pCore 2 C
  let restricted := line.subgroupOf core
  let layer := frattini core ⊔ restricted
  let conjugation : C →* MulAut core := MulAut.conjNormal
  have hfixed (actor : C) (vector : core) (hvector : vector ∈ restricted) :
      conjugation actor vector = vector := by
    apply Subtype.ext
    change actor * (vector : C) * actor⁻¹ = (vector : C)
    have hcomm := Subgroup.mem_center_iff.mp (hcenter hvector) actor
    change actor * (vector : C) = (vector : C) * actor at hcomm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hmap (actor : C) : layer.map (conjugation actor).toMonoidHom = layer := by
    change (frattini core ⊔ restricted).map _ = _
    rw [Subgroup.map_sup,
      Subgroup.characteristic_iff_map_eq.mp inferInstance (conjugation actor)]
    have heq : restricted.map (conjugation actor).toMonoidHom = restricted := by
      apply le_antisymm
      · rintro vector ⟨original, horiginal, rfl⟩
        change conjugation actor original ∈ restricted
        rwa [hfixed actor original horiginal]
      · intro vector hvector
        exact ⟨vector, hvector, hfixed actor vector hvector⟩
    rw [heq]
  let action : C →* MulAut (core ⧸ layer) :=
    { toFun actor := QuotientGroup.congr layer layer (conjugation actor) (hmap actor)
      map_one' := by
        apply MulEquiv.ext
        intro vector
        induction vector using Quotient.inductionOn with
        | h vector =>
          change QuotientGroup.mk' layer (conjugation 1 vector) =
            QuotientGroup.mk' layer vector
          rw [map_one]
          rfl
      map_mul' left right := by
        apply MulEquiv.ext
        intro vector
        induction vector using Quotient.inductionOn with
        | h vector =>
          change QuotientGroup.mk' layer (conjugation (left * right) vector) =
            QuotientGroup.mk' layer (conjugation left (conjugation right vector))
          rw [map_mul]
          rfl }
  have hformula (actor : C) (vector : core) :
      action actor (QuotientGroup.mk' layer vector) =
        QuotientGroup.mk' layer (conjugation actor vector) := rfl
  refine ⟨action, hformula, le_antisymm ?_ ?_⟩
  · let actors := action.ker.map conjugation
    have hactors : IsPGroup 2 actors := by
      apply fixed_central_frattini_automorphisms_isPGroup pCore_isPGroup actors restricted
      · intro actor vector hvector
        obtain ⟨original, _, heq⟩ := actor.property
        rw [← heq]
        exact hfixed original vector hvector
      · intro vector hvector
        apply Subtype.ext
        exact hexponent vector hvector
      · intro actor vector
        obtain ⟨original, horiginal, heq⟩ := actor.property
        change vector⁻¹ * (actor : MulAut core) vector ∈ layer
        rw [← heq]
        apply QuotientGroup.eq.mp
        have hh := DFunLike.congr_fun (MonoidHom.mem_ker.mp horiginal)
          (QuotientGroup.mk' layer vector)
        rw [hformula] at hh
        exact hh.symm
    have hconjugationKernel : conjugation.ker ≤ core := by
      intro actor hactor
      apply hcharacteristic
      apply Subgroup.mem_centralizer_iff.mpr
      intro vector hvector
      have heq := DFunLike.congr_fun (MonoidHom.mem_ker.mp hactor) ⟨vector, hvector⟩
      have hh := congrArg Subtype.val heq
      change actor * vector * actor⁻¹ = vector at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hpreimage := hactors.comap_of_ker_isPGroup conjugation
      (pCore_isPGroup.to_le hconjugationKernel)
    have hkernelTwo : IsPGroup 2 action.ker := hpreimage.to_le
      (Subgroup.le_comap_map conjugation action.ker)
    exact le_sSup ⟨inferInstance, hkernelTwo⟩
  · intro actor hactor
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro vector
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective layer vector
    rw [hformula]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply (show frattini core ≤ layer from le_sup_left)
    have hker := frattini_core_conjugation_kernel_eq hcharacteristic
    have hmem : actor ∈ ((Subgroup.quotientAut (frattini core)).comp conjugation).ker :=
      hker.symm ▸ hactor
    have heq := DFunLike.congr_fun (MonoidHom.mem_ker.mp hmem)
      (QuotientGroup.mk' (frattini core) original)
    rw [MonoidHom.comp_apply, Subgroup.quotientAut_apply_mk] at heq
    exact QuotientGroup.eq_iff_div_mem.mp heq

public theorem nine_three_final_core_frattini_mixed_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hgeometry :
      let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
      let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
        ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
      Nat.card mixed = 2 ∧ ∃ conjugator : G,
        conjugator ∈ GAt ctx.Γ ctx.criticalPath.a ∧
        T.map (MulAut.conj conjugator).toMonoidHom ≤
          Subgroup.centralizer (mixed : Set G)) :
    let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
      ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
    let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
    let line := (mixed.map embedding).subgroupOf centralizer
    ∃ normal : line.Normal,
      letI := normal
      let core := pCore 2 centralizer
      let layer := frattini core ⊔ line.subgroupOf core
      IsElementaryAbelian 2 (core ⧸ layer) ∧
        ∃ action : centralizer →* MulAut (core ⧸ layer),
          (∀ actor : centralizer, ∀ vector : core,
            action actor (QuotientGroup.mk' layer vector) =
              QuotientGroup.mk' layer (MulAut.conjNormal actor vector)) ∧
          action.ker = core := by
  let vertex := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
  let mixed := (⁅ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ vertex,
    ZAt ctx.Γ vertex ⊓ GAt ctx.Γ ctx.criticalPath.a⁆ : Subgroup G)
  let centralizer := Subgroup.centralizer (mixed.map embedding : Set H)
  let line := (mixed.map embedding).subgroupOf centralizer
  have hcenter : line ≤ Subgroup.center centralizer :=
    (nine_three_final_centralizer_center_core ctx hb hlarge first second config).2.trans
      inf_le_left
  have hnormal : line.Normal := by
    constructor
    intro vector hvector actor
    have heq := Subgroup.mem_center_iff.mp (hcenter hvector) actor
    simpa only [heq, mul_assoc, mul_inv_cancel, mul_one] using hvector
  let _ := hnormal
  refine ⟨hnormal, ?_⟩
  let core := pCore 2 centralizer
  let layer := frattini core ⊔ line.subgroupOf core
  change IsElementaryAbelian 2 (core ⧸ layer) ∧ _
  have hexponent : ∀ vector ∈ line, vector ^ 2 = 1 := by
    intro vector hvector
    obtain ⟨original, horiginal, heq⟩ := hvector
    have hcard : Nat.card mixed = 2 := hgeometry.1
    have hpow : (⟨original, horiginal⟩ : mixed) ^ 2 = 1 := by
      rw [← hcard]
      exact pow_card_eq_one' (x := (⟨original, horiginal⟩ : mixed))
    have hp := congrArg (fun value : mixed => embedding (value : G)) hpow
    apply Subtype.ext
    have heq' : embedding original = vector.val := heq
    change vector.val ^ 2 = 1
    rw [← heq']
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using hp
  refine ⟨Subgroup.elementary_quotient_of_frattini_le pCore_isPGroup layer le_sup_left, ?_⟩
  exact exists_core_frattini_central_action
    (nine_three_final_centralizer_setup_of_mixed_sylow ctx first second config hgeometry).2.1
    line hcenter hexponent

end Stellmacher.SectionNine
