module

public import Theory.Representation.CardFourCommutingActions
public import Theory.GroupAction.Quotient
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.Comparator.Defs
public import Theory.GroupAction.Extraspecial27CenterAction

/-!
# The fixed layer of the extraspecial order-27 action

Let D be the involution displacement and C its fixed subgroup. Their orders
are four and sixteen. The mapped center of the extraspecial actor acts
faithfully on D and has full commutator action on the whole binary module.
An actor normalizing the extraspecial group and fixing D pointwise therefore
centralizes its center. Coprime fixed-point lifting makes the center action
on C/D fixed-point-free. The centralizer of its order-three image in GL₂(2)
has order three, so a commuting two-group acts trivially on C/D.

The principal theorem supplies the middle-layer hypothesis of
`Subgroup.frattini_displacement_le_of_fixed_layer_action`, without assuming
any chief-factor recognition or classification of the module normalizer.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.47 / PDF p.37,
the extraspecial alternative immediately before (10).
-/

@[expose] public section

open scoped IsMulCommutative

namespace Extraspecial27FixedLayer

universe uD uQ uU

private theorem glTwoTwo_center_eq_bot :
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x = 1 := Subsingleton.elim _ _
    simp [hx]
  · intro hA
    have hAone : A = 1 := by simpa using hA
    subst A
    exact ⟨1, by simp⟩

/-- A finite two-group acting on the four-point elementary abelian group and
commuting with a faithful order-three action acts trivially. -/
theorem actsTrivially_card_four_of_commuting_three_two_group
    {D : Type uD} {Q : Type uQ} {U : Type uU}
    [Group D] [Group Q] [Group U] [Finite D] [Finite Q] [Finite U]
    [IsElementaryAbelian 2 U]
    [MulDistribMulAction D U] [MulDistribMulAction Q U]
    (hUcard : Nat.card U = 4)
    (hDcard : Nat.card D = 3)
    (hDfaith : Function.Injective
      (Representation.ofElementaryAbelianAction (A := D) (G := U) (p := 2)).asGroupHom)
    (hQgroup : IsPGroup 2 Q)
    (hcomm : ∀ d : D, ∀ q : Q, ∀ u : U,
      d • (q • u) = q • (d • u)) :
    ActsTrivially (A := Q) (G := U) := by
  let nU := Module.finrank (ZMod 2) (Additive U)
  have hnU : nU = 2 := by
    have hc : Nat.card (Additive U) = 4 := by
      calc
        Nat.card (Additive U) = Nat.card U := Nat.card_congr Additive.toMul
        _ = 4 := hUcard
    rw [@Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive U)] at hc
    norm_num at hc
    change 2 ^ nU = 2 ^ 2 at hc
    exact Nat.pow_right_injective (by omega) hc
  let b : Module.Basis (Fin 2) (ZMod 2) (Additive U) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive U) hnU
  let ρD := Representation.ofElementaryAbelianAction (A := D) (G := U) (p := 2)
  let ρQ := Representation.ofElementaryAbelianAction (A := Q) (G := U) (p := 2)
  let φD : D →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρD.asGroupHom
  let φQ : Q →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρQ.asGroupHom
  have hφDinj : Function.Injective φD :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hDfaith
  have hGLcard :
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hφDcard : Nat.card φD.range = 3 := by
    calc
      Nat.card φD.range = Nat.card D :=
        Nat.card_congr
          (Equiv.ofBijective φD.rangeRestrict
            ⟨fun x y hxy => hφDinj (congrArg Subtype.val hxy),
              φD.rangeRestrict_surjective⟩).symm
      _ = 3 := hDcard
  have hρcomm (d : D) (q : Q) : Commute (ρD.asGroupHom d) (ρQ.asGroupHom q) := by
    apply Units.ext
    apply LinearMap.ext
    intro u
    exact congrArg Additive.ofMul (hcomm d q (Additive.toMul u))
  have hφcomm (d : D) (q : Q) : Commute (φD d) (φQ q) := by
    change (Matrix.GeneralLinearGroup.toLin' b).symm (ρD.asGroupHom d) *
        (Matrix.GeneralLinearGroup.toLin' b).symm (ρQ.asGroupHom q) =
      (Matrix.GeneralLinearGroup.toLin' b).symm (ρQ.asGroupHom q) *
        (Matrix.GeneralLinearGroup.toLin' b).symm (ρD.asGroupHom d)
    rw [← map_mul, (hρcomm d q).eq, map_mul]
  let C := Subgroup.centralizer (φD.range : Set
    (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))
  let hthree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (Nat.Prime 3) := hthree
  let hφDcyclic : IsCyclic φD.range := isCyclic_of_prime_card hφDcard
  let _ : IsMulCommutative φD.range := hφDcyclic.isMulCommutative
  have hφDleC : φD.range ≤ C := by
    simpa only [C] using Subgroup.le_centralizer φD.range
  have hthree_dvd_C : 3 ∣ Nat.card C := by
    simpa only [hφDcard] using Subgroup.card_dvd_of_le hφDleC
  have hC_dvd_six : Nat.card C ∣ 6 := by
    simpa only [hGLcard] using Subgroup.card_subgroup_dvd_card C
  have hCcard : Nat.card C = 3 := by
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hCle : Nat.card C ≤ 6 := Nat.le_of_dvd (by norm_num) hC_dvd_six
    obtain ⟨k, hk⟩ := hthree_dvd_C
    have hcases : Nat.card C = 3 ∨ Nat.card C = 6 := by
      omega
    rcases hcases with hthree | hsix
    · exact hthree
    · have hCtop : C = ⊤ :=
        Subgroup.eq_top_of_card_eq C (by rw [hGLcard]; exact hsix)
      have hcenter :
          Subgroup.center
              (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = ⊥ :=
        glTwoTwo_center_eq_bot
      have hφDcenter : φD.range ≤ Subgroup.center
          (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) := by
        exact (Subgroup.centralizer_eq_top_iff_subset.mp (by
          simpa only [C] using hCtop))
      rw [hcenter] at hφDcenter
      have hφDbot : φD.range = ⊥ := le_antisymm hφDcenter bot_le
      have hcardOne : Nat.card φD.range = 1 := by rw [hφDbot]; simp
      omega
  have hφQleC : φQ.range ≤ C := by
    rintro x ⟨q, rfl⟩
    change φQ q ∈ Subgroup.centralizer (φD.range : Set
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨d, rfl⟩
    exact (hφcomm d q).eq
  have hφQ_dvd_three : Nat.card φQ.range ∣ 3 := by
    simpa only [hCcard] using Subgroup.card_dvd_of_le hφQleC
  obtain ⟨power, hpower⟩ := hQgroup.exists_card_eq
  have hφQ_dvd_two : Nat.card φQ.range ∣ 2 ^ power := by
    simpa only [hpower] using Subgroup.card_range_dvd φQ
  have hφQcard : Nat.card φQ.range = 1 := by
    exact Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_right power)
      hφQ_dvd_three hφQ_dvd_two
  have hφQbot : φQ.range = ⊥ := Subgroup.card_eq_one.mp hφQcard
  intro q u
  have hφQone : φQ q = 1 := by
    have hmem : φQ q ∈ φQ.range := ⟨q, rfl⟩
    rw [hφQbot] at hmem
    simpa using hmem
  have hρQone : ρQ.asGroupHom q = 1 := by
    apply (Matrix.GeneralLinearGroup.toLin' b).symm.injective
    change φQ q = (Matrix.GeneralLinearGroup.toLin' b).symm 1
    simpa only [map_one] using hφQone
  have happ := congrArg
    (fun f : LinearMap.GeneralLinearGroup (ZMod 2) (Additive U) =>
      LinearMap.GeneralLinearGroup.toLinearEquiv f (Additive.ofMul u)) hρQone
  change ρQ q (Additive.ofMul u) = Additive.ofMul u at happ
  apply Additive.ofMul.injective
  simpa [ρQ] using happ

theorem faithful_card_three_of_fixed_bot
    {Z U : Type*} [Group Z] [Group U] [Finite Z] [Finite U]
    [IsElementaryAbelian 2 U] [MulDistribMulAction Z U]
    (hZcard : Nat.card Z = 3) (hUcard : Nat.card U = 4)
    (hfixed : FixedPoints.subgroup Z U = ⊥) :
    Function.Injective
      (Representation.ofElementaryAbelianAction (A := Z) (G := U) (p := 2)).asGroupHom := by
  let representation := Representation.ofElementaryAbelianAction (A := Z) (G := U) (p := 2)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  have hdiv : Nat.card representation.asGroupHom.ker ∣ 3 := by
    simpa only [hZcard] using Subgroup.card_subgroup_dvd_card representation.asGroupHom.ker
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdiv with hone | hthree
  · exact Subgroup.card_eq_one.mp hone
  · have hker : representation.asGroupHom.ker = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (hthree.trans hZcard.symm)
    have htrivial (actor : Z) (point : U) : actor • point = point := by
      have hactor : representation.asGroupHom actor = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [hker]
        trivial
      have happ := congrArg
        (fun linear : LinearMap.GeneralLinearGroup (ZMod 2) (Additive U) =>
          LinearMap.GeneralLinearGroup.toLinearEquiv linear (Additive.ofMul point)) hactor
      exact Additive.ofMul.injective happ
    have htop : FixedPoints.subgroup Z U = ⊤ := by
      apply top_unique
      intro point _ actor
      exact htrivial actor point
    have hcard : Nat.card U = 1 := by
      have hsub := congrArg (fun subgroup : Subgroup U => Nat.card subgroup)
        (htop.symm.trans hfixed)
      simpa using hsub
    omega

theorem displacement_mem_of_four_element_quotient
    {Z Q U : Type*} [Group Z] [Group Q] [Group U]
    [Finite Z] [Finite Q] [Finite U] [IsElementaryAbelian 2 U]
    [MulDistribMulAction Z U] [MulDistribMulAction Q U]
    (layer : Subgroup U)
    (hZinvariant : IsInvariant Z U layer)
    (hQinvariant : IsInvariant Q U layer)
    (hZcard : Nat.card Z = 3) (hQgroup : IsPGroup 2 Q)
    (hlayer : Nat.card layer = 4) (hquotient : Nat.card (U ⧸ layer) = 4)
    (hfixed : FixedPoints.subgroup Z U = ⊥)
    (hcommutes : ∀ central : Z, ∀ actor : Q, ∀ point : U,
      central • (actor • point) = actor • (central • point)) :
    ∀ actor : Q, ∀ point : U, point⁻¹ * (actor • point) ∈ layer := by
  let _ : IsElementaryAbelian 2 (U ⧸ layer) := {
    exponent_dvd_p := (Group.exponent_quotient_dvd layer).trans
      (IsElementaryAbelian.exponent_dvd_p 2 U) }
  let _ : MulDistribMulAction Z (U ⧸ layer) :=
    quotientMulDistribMulAction layer hZinvariant
  let _ : MulDistribMulAction Q (U ⧸ layer) :=
    quotientMulDistribMulAction layer hQinvariant
  have hquotientFixed : FixedPoints.subgroup Z (U ⧸ layer) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_isMulCommutative layer hZinvariant
      (by rw [hZcard, hlayer]; decide), hfixed, Subgroup.map_bot]
  have hfaith := faithful_card_three_of_fixed_bot hZcard hquotient hquotientFixed
  have hquotientCommutes (central : Z) (actor : Q) (point : U ⧸ layer) :
      central • (actor • point) = actor • (central • point) := by
    refine QuotientGroup.induction_on point ?_
    intro representative
    change QuotientGroup.mk' layer (central • (actor • representative)) =
      QuotientGroup.mk' layer (actor • (central • representative))
    rw [hcommutes]
  have htrivial := actsTrivially_card_four_of_commuting_three_two_group
    hquotient hZcard hfaith hQgroup hquotientCommutes
  intro actor point
  apply (QuotientGroup.eq_one_iff (N := layer) _).mp
  change QuotientGroup.mk' layer (point⁻¹ * (actor • point)) = 1
  rw [map_mul, map_inv, inv_mul_eq_one]
  exact (htrivial actor (QuotientGroup.mk' layer point)).symm

theorem normalizer_preserves_mapped_center
    {G : Type*} [Group G] (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤
      Subgroup.normalizer
        (((Subgroup.center subgroup).map subgroup.subtype : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor point hpoint
  rcases Subgroup.mem_map.mp hpoint with ⟨representative, hrepresentative, rfl⟩
  let normalizingActor : Subgroup.normalizer (subgroup : Set G) := ⟨actor, hactor⟩
  have hfixed :
      Subgroup.comap (Subgroup.normalizerMonoidHom subgroup normalizingActor).toMonoidHom
        (Subgroup.center subgroup) = Subgroup.center subgroup :=
    (inferInstance : (Subgroup.center subgroup).Characteristic).fixed
      (Subgroup.normalizerMonoidHom subgroup normalizingActor)
  have himage : Subgroup.normalizerMonoidHom subgroup normalizingActor representative ∈
      Subgroup.center subgroup := by
    change representative ∈ Subgroup.comap
      (Subgroup.normalizerMonoidHom subgroup normalizingActor).toMonoidHom
        (Subgroup.center subgroup)
    rwa [hfixed]
  exact ⟨Subgroup.normalizerMonoidHom subgroup normalizingActor representative, himage, by
    simp [normalizingActor, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

theorem centralizes_center_of_fixes_faithful_layer
    {W : Type*} [Group W]
    (oddGroup actors : Subgroup (MulAut W)) (layer : Subgroup W)
    (hinvariant : IsInvariant ((Subgroup.center oddGroup).map oddGroup.subtype) W layer)
    (hnormalizes : actors ≤ Subgroup.normalizer (oddGroup : Set (MulAut W)))
    (hfixes : ∀ actor : actors, ∀ point ∈ layer, (actor : MulAut W) point = point)
    (hfaithful : ∀ central : (Subgroup.center oddGroup).map oddGroup.subtype,
      (∀ point ∈ layer, (central : MulAut W) point = point) → central = 1) :
    ∀ actor : actors, ∀ central : (Subgroup.center oddGroup).map oddGroup.subtype,
      Commute (actor : MulAut W) (central : MulAut W) := by
  let center := (Subgroup.center oddGroup).map oddGroup.subtype
  let _ : IsInvariant center W layer := hinvariant
  have hfaith : Function.Injective (MulDistribMulAction.toMulAut center layer) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [Subgroup.eq_bot_iff_forall]
    intro central hcentral
    apply hfaithful central
    intro point hpoint
    have heq := DFunLike.congr_fun (MonoidHom.mem_ker.mp hcentral) (⟨point, hpoint⟩ : layer)
    exact congrArg Subtype.val heq
  intro actor central
  have hnormalize : (actor : MulAut W) ∈ Subgroup.normalizer (center : Set (MulAut W)) :=
    normalizer_preserves_mapped_center oddGroup (hnormalizes actor.property)
  let conjugated : center := ⟨(actor : MulAut W) * (central : MulAut W) *
    (actor : MulAut W)⁻¹,
    (Subgroup.mem_normalizer_iff.mp hnormalize _).mp central.property⟩
  have hequal : conjugated = central := by
    apply hfaith
    ext point
    change (actor : MulAut W) ((central : MulAut W) ((actor : MulAut W)⁻¹ (point : W))) =
      (central : MulAut W) (point : W)
    rw [show (↑actor : MulAut W)⁻¹ (point : W) = point from hfixes actor⁻¹ point point.property]
    apply hfixes actor
    exact (IsInvariant.invariant (A := center) (H := layer) central point).mp point.property
  have hconjugated := congrArg Subtype.val hequal
  exact (mul_inv_eq_iff_eq_mul).mp hconjugated

theorem fixed_layer_displacement_of_center_action
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (oddGroup actors : Subgroup (MulAut W))
    (hZcard : Nat.card (Subgroup.center oddGroup) = 3)
    (hspace : Nat.card W = 64)
    (htwo : IsPGroup 2 actors)
    (hnormalizes : actors ≤ Subgroup.normalizer (oddGroup : Set (MulAut W)))
    (involution : actors) (hinvolution : IsInvolution (involution : MulAut W))
    (hcenter : ⁅(Subgroup.center oddGroup).map oddGroup.subtype,
      Subgroup.zpowers (involution : MulAut W)⁆ = ⊥)
    (hindex : Nat.card W = 4 * Nat.card
      (FixedPoints.subgroup (Subgroup.zpowers (involution : MulAut W)) W))
    (hcommutes : ∀ actor : actors,
      Commute (actor : MulAut W) (involution : MulAut W))
    (hfixes : ∀ actor : actors,
      ∀ point ∈ commutatorAction (Subgroup.zpowers (involution : MulAut W)) W,
        (actor : MulAut W) point = point)
    (hZfull : commutatorAction ((Subgroup.center oddGroup).map oddGroup.subtype) W = ⊤)
    (hZfaith : ∀ central : (Subgroup.center oddGroup).map oddGroup.subtype,
      (∀ point ∈ commutatorAction (Subgroup.zpowers (involution : MulAut W)) W,
        (central : MulAut W) point = point) → central = 1) :
    ∀ actor : actors,
      ∀ point ∈ FixedPoints.subgroup (Subgroup.zpowers (involution : MulAut W)) W,
        point⁻¹ * (actor : MulAut W) point ∈
          commutatorAction (Subgroup.zpowers (involution : MulAut W)) W := by
  let center := (Subgroup.center oddGroup).map oddGroup.subtype
  let cyclic := Subgroup.zpowers (involution : MulAut W)
  let fixed := FixedPoints.subgroup cyclic W
  let displacement := commutatorAction cyclic W
  have hcenterCard : Nat.card center = 3 := by
    rw [Subgroup.card_map_of_injective oddGroup.subtype_injective]
    exact hZcard
  have hcyclicCard : Nat.card cyclic = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hinvolution.2 hinvolution.1
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let generator : cyclic := ⟨(involution : MulAut W), Subgroup.mem_zpowers _⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq), Subtype.ext hinvolution.2⟩
  obtain ⟨hcount, hdisplacementFixed⟩ :=
    card_two_action_fixed_commutator_card_data (U := W) generator hgenerator hcyclicCard
  have hfixedCard : Nat.card fixed = 16 := by
    change Nat.card W = 4 * Nat.card fixed at hindex
    omega
  have hdisplacementCard : Nat.card displacement = 4 := by
    change Nat.card W = Nat.card fixed * Nat.card displacement at hcount
    rw [hspace, hfixedCard] at hcount
    omega
  have hcenterNormalizes : center ≤ Subgroup.normalizer (cyclic : Set (MulAut W)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenter).trans
      (Subgroup.centralizer_le_normalizer _)
  have hactorsNormalizes : actors ≤ Subgroup.normalizer (cyclic : Set (MulAut W)) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro actor hactor
    rw [Subgroup.mem_centralizer_iff]
    intro power hpower
    obtain ⟨integer, rfl⟩ := Subgroup.mem_zpowers_iff.mp hpower
    exact ((hcommutes ⟨actor, hactor⟩).zpow_right integer).eq.symm
  let _ : IsInvariant center W displacement :=
    commutatorAction_isInvariant_of_normalizing_actor center cyclic hcenterNormalizes
  let _ : IsInvariant actors W displacement :=
    commutatorAction_isInvariant_of_normalizing_actor actors cyclic hactorsNormalizes
  let _ : IsInvariant center W fixed :=
    fixedPoints_isInvariant_of_normalizing_actor center cyclic hcenterNormalizes
  let _ : IsInvariant actors W fixed :=
    fixedPoints_isInvariant_of_normalizing_actor actors cyclic hactorsNormalizes
  let _ : IsElementaryAbelian 2 fixed := {
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom fixed.subtype fixed.subtype_injective).trans
      (IsElementaryAbelian.exponent_dvd_p 2 W) }
  have hcenterCommutes := centralizes_center_of_fixes_faithful_layer
    oddGroup actors displacement inferInstance hnormalizes hfixes hZfaith
  have hcenterFixed : FixedPoints.subgroup center W = ⊥ := by
    have hcompl :=
      isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := W) (A := center)
        (Group.isSolvable_of_comm fun first second =>
          (IsMulCommutative.is_comm (M := W)).comm first second)
        (by rw [hcenterCard, hspace]; decide) inferInstance
    apply le_antisymm _ bot_le
    intro point hpoint
    apply hcompl.disjoint.le_bot
    exact ⟨hpoint, by rw [hZfull]; trivial⟩
  have hcenterFixedRestricted : FixedPoints.subgroup center fixed = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro point hpoint
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← hcenterFixed]
    intro central
    exact congrArg Subtype.val (hpoint central)
  let layer := displacement.subgroupOf fixed
  have hlayerCard : Nat.card layer = 4 := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hdisplacementFixed).toEquiv).trans
      hdisplacementCard
  have hquotientCard : Nat.card (fixed ⧸ layer) = 4 := by
    have hquotientCount := layer.card_mul_index
    rw [Subgroup.index_eq_card, hlayerCard, hfixedCard] at hquotientCount
    omega
  have hdisplacement := displacement_mem_of_four_element_quotient
    (Z := center) (Q := actors) layer
    (isInvariant_subgroupOf displacement fixed)
    (isInvariant_subgroupOf displacement fixed)
    hcenterCard htwo hlayerCard hquotientCard hcenterFixedRestricted
    (fun central actor point => Subtype.ext
      (DFunLike.congr_fun (hcenterCommutes actor central).eq.symm (point : W)))
  intro actor point hpoint
  exact hdisplacement actor (⟨point, hpoint⟩ : fixed)

end Extraspecial27FixedLayer

theorem extraspecial27_fixed_layer_displacement_le
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (oddGroup actors : Subgroup (MulAut W))
    (hodd : IsExtraspecial 3 oddGroup)
    (hoddCard : Nat.card oddGroup = 27) (hspace : Nat.card W = 64)
    (hfull : commutatorAction oddGroup W = ⊤)
    (htwo : IsPGroup 2 actors)
    (hnormalizes : actors ≤ Subgroup.normalizer (oddGroup : Set (MulAut W)))
    (involution : actors)
    (hinvolution : IsInvolution (involution : MulAut W))
    (hgenerates : ⁅oddGroup, Subgroup.zpowers (involution : MulAut W)⁆ = oddGroup)
    (hcenter : ⁅(Subgroup.center oddGroup).map oddGroup.subtype,
      Subgroup.zpowers (involution : MulAut W)⁆ = ⊥)
    (hindex : Nat.card W = 4 * Nat.card
      (FixedPoints.subgroup (Subgroup.zpowers (involution : MulAut W)) W))
    (hcommutes : ∀ actor : actors,
      Commute (actor : MulAut W) (involution : MulAut W))
    (hfixes : ∀ actor : actors,
      ∀ point ∈ commutatorAction (Subgroup.zpowers (involution : MulAut W)) W,
        (actor : MulAut W) point = point) :
    ∀ actor : actors,
      ∀ point ∈ FixedPoints.subgroup (Subgroup.zpowers (involution : MulAut W)) W,
        point⁻¹ * (actor : MulAut W) point ∈
          commutatorAction (Subgroup.zpowers (involution : MulAut W)) W := by
  let _ : IsExtraspecial 3 oddGroup := hodd
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let cyclic := Subgroup.zpowers (involution : MulAut W)
  let generator : cyclic := ⟨(involution : MulAut W), Subgroup.mem_zpowers _⟩
  have hgenerator : generator ≠ 1 ∧ generator ^ 2 = 1 :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq), Subtype.ext hinvolution.2⟩
  have hcyclicCard : Nat.card cyclic = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hinvolution.2 hinvolution.1
  have hcount :=
    (card_two_action_fixed_commutator_card_data (U := W) generator hgenerator hcyclicCard).1
  have hdisplacement : Nat.card (commutatorAction cyclic W) = 4 := by
    change Nat.card W = 4 * Nat.card (FixedPoints.subgroup cyclic W) at hindex
    have hfixedCard : Nat.card (FixedPoints.subgroup cyclic W) = 16 := by omega
    rw [hspace, hfixedCard] at hcount
    omega
  obtain ⟨hZfull, hZfaith⟩ := extraspecial27_center_action oddGroup hodd hoddCard
    (involution : MulAut W) hinvolution (hnormalizes involution.property)
    hfull hgenerates hcenter hdisplacement
  exact Extraspecial27FixedLayer.fixed_layer_displacement_of_center_action oddGroup actors
    (IsExtraspecial.center_order_p 3 oddGroup) hspace htwo hnormalizes involution hinvolution
    hcenter hindex hcommutes hfixes hZfull hZfaith
