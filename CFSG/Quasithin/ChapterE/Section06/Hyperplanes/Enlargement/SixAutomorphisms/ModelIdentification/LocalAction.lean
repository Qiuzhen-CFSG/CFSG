module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.SylowSubnormalIntersection
public import CFSG.Quasithin.ChapterA.Section02.Statements

/-!
# The actual action in the A₆ further enlargement

For X < Y, component restriction forces A to act nontrivially on Y. Its
kernel contains A₁ = A ∩ Uᵍ, of index at most two in A, so the induced
A-action has order two and kernel A₁. Since C_V(X) = A, the whole V-action
has kernel A₁ and order eight. The embedded A₆ remains a component of the
literal fixed subgroup of this action, and embeds faithfully in both
Inn(Y) and Y/Z(Y).

The common Sylow Q = C_T(V) is retained inside C_G(A), with its actual
intersection with X. E.6.21 gives Z(Y) = O₂(Y); it does not make this
center trivial. Exact universal Theorems A and C classify the central
quotient, with semisimplicity and section inheritance proved explicitly.
The final transport lemma still requires the binary quotient, trivial
center and outerness; no model inspection is claimed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265); E.6.5, E.6.21, and Theorems A and C on p.33.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
open ComponentBalance
universe u
variable {G : Type u} [Group G] [Finite G]
variable {M V U A L X Y : Subgroup G} {g : G}

omit [Finite G] in
/-- Restriction preserves the original component inside C_Y(A). -/
theorem component_in_fixed_centralizer
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    IsComponent ↥(Y ⊓ centralizer (A : Set G))
      (X.subgroupOf (Y ⊓ centralizer (A : Set G))) := by
  have hXC := d.six.component.1
  let _ := d.six.component.2.2
  exact ⟨d.six.component.2.1.comap (inclusion inf_le_right),
    IsQuasisimple.of_mulEquiv ((subgroupOfEquivOfLe hXC).trans
      (subgroupOfEquivOfLe (le_inf hY.proper.le hXC)).symm)⟩

omit [Finite G] in
/-- A proper containing component cannot also centralize all of A. -/
theorem not_centralizes
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    ¬ Y ≤ centralizer (A : Set G) := by
  intro hyc
  have hcc : centralizer (A : Set G) ≤ centralizer (intersection A U g : Set G) :=
    Subgroup.centralizer_le inf_le_left
  let _ := hY.component.2.2
  have hy : IsComponent (centralizer (A : Set G))
      (Y.subgroupOf (centralizer (A : Set G))) :=
    ⟨hY.component.2.1.comap (inclusion hcc),
      IsQuasisimple.of_mulEquiv ((subgroupOfEquivOfLe hY.component.1).trans
        (subgroupOfEquivOfLe hyc).symm)⟩
  have he := d.six.component.2.eq_of_le hy (fun _ hx => hY.proper.le hx)
  have he' := congrArg (Subgroup.map (centralizer (A : Set G)).subtype) he
  rw [map_subgroupOf_eq_of_le d.six.component.1, map_subgroupOf_eq_of_le hyc] at he'
  exact hY.proper.ne he'

omit [Finite G] in
/-- The full action image has cardinality equal to the actual centralizer index. -/
theorem actionImage_card (D Y : Subgroup G) (hn : D ≤ normalizer (Y : Set G)) :
    Nat.card (actionImage D Y) = (D ⊓ centralizer (Y : Set G)).relIndex D := by
  let f := Y.normalizerMonoidHom.comp (inclusion hn)
  have hk : f.ker = (centralizer (Y : Set G)).subgroupOf D := by
    ext d
    change inclusion hn d ∈ Y.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  rw [actionImage_eq_range hn, ← index_ker, hk, inf_relIndex_left]
  rfl

/-- Intersecting A with the conjugate hyperplane costs at most index two. -/
theorem intersection_index_le_two [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g) :
    (intersection A U g).relIndex A ≤ 2 := by
  have hp : (U.map (MulAut.conj g).toMonoidHom).relIndex V = 2 := by
    calc
      _ = 2 ^ subgroupCorank V (U.map (MulAut.conj g).toMonoidHom) := by
        rw [subgroupCorank_eq_quotient_finrank]
        exact relIndex_eq_two_pow_quotient_finrank V _
      _ = 2 := by rw [corank_conjugate V U g d.conjugator_mem.2, d.hyperplane.2]; rfl
  rw [intersection, inf_relIndex_left]
  exact (relIndex_le_of_le_right d.subspace_mem.1 (by rw [hp]; decide)).trans_eq hp

/-- The actual A-action is an involution, without any model classification. -/
theorem action_order_two [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    Nat.card (actionImage A Y) = 2 := by
  have hn : A ≤ normalizer (Y : Set G) :=
    d.subspace_mem.1.trans (hY.normalized_by_V d.subspace_mem.1)
  rw [actionImage_card A Y hn]
  have hi : intersection A U g ≤ A ⊓ centralizer (Y : Set G) :=
    le_inf inf_le_left (le_centralizer_iff.mpr hY.component.1)
  have hle : (A ⊓ centralizer (Y : Set G)).relIndex A ≤ 2 :=
    (relIndex_le_of_le_left hi ((intersection A U g).subgroupOf A).index_ne_zero_of_finite).trans
      (intersection_index_le_two d)
  have hne : (A ⊓ centralizer (Y : Set G)).relIndex A ≠ 1 := by
    intro he
    have hc := (relIndex_eq_one.mp he).trans inf_le_right
    exact not_centralizes d hY (le_centralizer_iff.mp hc)
  have hp : 0 < (A ⊓ centralizer (Y : Set G)).relIndex A :=
    Nat.pos_of_ne_zero ((A ⊓ centralizer (Y : Set G)).subgroupOf A).index_ne_zero_of_finite
  omega

/-- Its kernel in A is exactly A₁, not merely a subgroup containing A₁. -/
theorem action_kernel [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    A ⊓ centralizer (Y : Set G) = intersection A U g := by
  have hn := d.subspace_mem.1.trans (hY.normalized_by_V d.subspace_mem.1)
  have hc := action_order_two d hY
  rw [actionImage_card A Y hn] at hc
  have hi : intersection A U g ≤ A ⊓ centralizer (Y : Set G) :=
    le_inf inf_le_left (le_centralizer_iff.mpr hY.component.1)
  have hmul := relIndex_mul_relIndex (intersection A U g)
    (A ⊓ centralizer (Y : Set G)) A hi inf_le_left
  rw [hc] at hmul
  have hle := intersection_index_le_two d
  have hp := Nat.pos_of_ne_zero
    ((intersection A U g).subgroupOf (A ⊓ centralizer (Y : Set G))).index_ne_zero_of_finite
  change 0 < (intersection A U g).relIndex (A ⊓ centralizer (Y : Set G)) at hp
  have he : (intersection A U g).relIndex (A ⊓ centralizer (Y : Set G)) = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp he) hi

/-- The full V-action has the same kernel, using the original fixed-space equality. -/
theorem fixed_space [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    V ⊓ centralizer (Y : Set G) = intersection A U g := by
  rw [← action_kernel d hY]
  apply le_antisymm
  · exact le_inf ((inf_le_inf_left V (Subgroup.centralizer_le hY.proper.le)).trans
      d.six.fixed.le) inf_le_right
  · exact inf_le_inf_right _ d.subspace_mem.1

/-- Strict enlargement forces the intersection to have corank exactly three. -/
theorem intersection_corank [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    subgroupCorank V (intersection A U g) = 3 := by
  have hn := d.subspace_mem.1.trans (hY.normalized_by_V d.subspace_mem.1)
  have hc := action_order_two d hY
  rw [actionImage_card A Y hn, action_kernel d hY] at hc
  have hp : A.relIndex V = 4 := by
    calc
      _ = 2 ^ subgroupCorank V A := by
        rw [subgroupCorank_eq_quotient_finrank]
        exact relIndex_eq_two_pow_quotient_finrank V A
      _ = 4 := by rw [d.corank]
                  rfl
  have hmul := relIndex_mul_relIndex (intersection A U g) A V inf_le_left d.subspace_mem.1
  rw [hc, hp] at hmul
  change Nat.log 2 ((intersection A U g).relIndex V) = 3
  rw [← hmul]
  decide

/-- The full action induced by V has order eight. -/
theorem whole_action_order [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    Nat.card (actionImage V Y) = 8 := by
  rw [actionImage_card V Y (hY.normalized_by_V d.subspace_mem.1), fixed_space d hY]
  calc
    _ = 2 ^ subgroupCorank V (intersection A U g) := by
      rw [subgroupCorank_eq_quotient_finrank]
      exact relIndex_eq_two_pow_quotient_finrank V _
    _ = 8 := by rw [intersection_corank d hY]
                rfl

omit [Finite G] in
/-- Quasisimplicity transfers from the relative component to the actual subgroup. -/
theorem extension_quasisimple (hY : NormalComponentExtension U A X g Y) :
    IsQuasisimple Y := by
  let _ := hY.component.2.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hY.component.1)

/-- E.6.21 leaves a central two-cover; it does not establish a simple model. -/
theorem extension_center
    (d : EscapeConfiguration M V U A L X g) (hne : intersection A U g ≠ ⊥)
    (ho : OddCoreFree V) (hY : NormalComponentExtension U A X g Y) :
    center Y = pCore 2 Y := by
  let _ := extension_quasisimple hY
  have hb := hY.component.2.1.pPrimeCore_eq_bot
    (ho _ (inf_le_left.trans d.subspace_mem.1) hne)
    (Y.subgroupOf (centralizer (intersection A U g : Set G)))
  have ht := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hY.component.1)
  rw [hb, Subgroup.map_bot] at ht
  exact IsQuasisimple.center_eq_pCore ht.symm

/-- Keep the source Q, its Sylow property in C_G(A), and its centralization by V. -/
theorem common_sylow {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (d : EscapeConfiguration M V U A L X g) :
    (∃ S : Sylow 2 (centralizer (A : Set G)),
      (S : Subgroup (centralizer (A : Set G))).map (centralizer (A : Set G)).subtype =
        sylowCentralizer (T : Subgroup G) V) ∧
    V ≤ sylowCentralizer (T : Subgroup G) V ∧
    V ≤ centralizer (sylowCentralizer (T : Subgroup G) V : Set G) :=
  ⟨h.sylow_obstruction d.subspace_mem, h.le_sylowCentralizer,
    le_centralizer_iff.mpr inf_le_right⟩

/-- The same Q meets the embedded A₆ in a Sylow subgroup of that A₆. -/
theorem component_sylow {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (d : EscapeConfiguration M V U A L X g) :
    ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype =
      sylowCentralizer (T : Subgroup G) V ⊓ X := by
  obtain ⟨S, hS⟩ := h.sylow_obstruction d.subspace_mem
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal _ d.six.component.2.1
  let e := subgroupOfEquivOfLe d.six.component.1
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((P : Subgroup _).map e.toMonoidHom).map X.subtype = _
  rw [hP, map_map]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hS ▸ mem_map.mpr ⟨y.1, hy, rfl⟩, y.2⟩
  · rintro ⟨hxS, hxX⟩
    obtain ⟨t, ht, he⟩ := mem_map.mp (hS.symm ▸ hxS)
    change (t : G) = x at he
    have htX : (t : G) ∈ X := he.symm ▸ hxX
    exact ⟨⟨t, htX⟩, ht, he⟩

omit [Finite G] in
/-- The fixed subgroup of the whole recorded action is the literal centralizer. -/
theorem fixed_subgroup_eq (D Y : Subgroup G) (hn : D ≤ normalizer (Y : Set G)) :
    FixedPoints.subgroup (actionImage D Y) Y = (centralizer (D : Set G)).subgroupOf Y := by
  ext y
  constructor
  · intro hy d hd
    have hi : Y.normalizerMonoidHom (inclusion hn ⟨d, hd⟩) ∈ actionImage D Y := by
      rw [actionImage_eq_range hn]
      exact ⟨⟨d, hd⟩, rfl⟩
    have he := congrArg Subtype.val (hy ⟨_, hi⟩)
    change d * (y : G) * d⁻¹ = y at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hy r
    obtain ⟨d, hd, he⟩ := r.property
    apply Subtype.ext
    change (r.val y : G) = y
    rw [← he]
    change (d : G) * (y : G) * (d : G)⁻¹ = y
    exact mul_inv_eq_iff_eq_mul.mpr (hy d hd)

omit [Finite G] in
/-- Identify the actual A₆ component in the common fixed subgroup of Aut_A(Y). -/
theorem six_fixed_component [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    X.subgroupOf Y ≤ FixedPoints.subgroup (actionImage A Y) Y ∧
    IsComponent (FixedPoints.subgroup (actionImage A Y) Y)
      ((X.subgroupOf Y).subgroupOf (FixedPoints.subgroup (actionImage A Y) Y)) ∧
    Chapter1.Section02.LocalModels.IsAlternating (X.subgroupOf Y) 6 := by
  have hn := d.subspace_mem.1.trans (hY.normalized_by_V d.subspace_mem.1)
  rw [fixed_subgroup_eq A Y hn]
  let C := centralizer (A : Set G)
  let e : ↥(Y ⊓ C) ≃* C.subgroupOf Y :=
    { toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have he : (X.subgroupOf (Y ⊓ C)).map e.toMonoidHom =
      (X.subgroupOf Y).subgroupOf (C.subgroupOf Y) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  obtain ⟨f⟩ := d.six.model
  exact ⟨fun _ hx => d.six.component.1 hx,
    he ▸ (component_in_fixed_centralizer d hY).map_equiv e,
    ⟨(subgroupOfEquivOfLe hY.proper.le).trans f⟩⟩

omit [Finite G] in
/-- The embedded A₆ has trivial center, using its actual alternating equivalence. -/
theorem six_center_eq_bot (d : EscapeConfiguration M V U A L X g) : center X = ⊥ := by
  obtain ⟨e⟩ := d.six.model
  apply le_bot_iff.mp
  intro x hx
  have he := (centerCongr e ⟨x, hx⟩).property
  change e x ∈ center (alternatingGroup (Fin 6)) at he
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

omit [Finite G] in
/-- The actual A₆ embeds faithfully in Inn(Y), even before removing Z(Y). -/
theorem six_inner_embedding_injective
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    Function.Injective ((MulAut.conj : Y →* MulAut Y).comp (inclusion hY.proper.le)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have hz : x ∈ center X := by
    apply mem_center_iff.mpr
    intro y
    have he := congrArg (fun a : MulAut Y => (a (inclusion hY.proper.le y) : G)) hx
    change (x : G) * (y : G) * (x : G)⁻¹ = y at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  rwa [six_center_eq_bot d] at hz

omit [Finite G] in
/-- The actual A₆ survives faithfully in the central quotient of Y. -/
theorem six_quotient_embedding_injective
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    Function.Injective ((QuotientGroup.mk' (center Y)).comp (inclusion hY.proper.le)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  have hc : inclusion hY.proper.le x ∈ center Y := (QuotientGroup.eq_one_iff _).mp hx
  have hz : x ∈ center X := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (congrArg (fun z : Y => (z : G))
      ((mem_center_iff.mp hc) (inclusion hY.proper.le y)))
  rwa [six_center_eq_bot d] at hz

/-- The nonidentity subspace centralizer, and hence Y, is SQTK. -/
theorem extension_sqtk {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (d : EscapeConfiguration M V U A L X g)
    (hne : intersection A U g ≠ ⊥) (hY : NormalComponentExtension U A X g Y) :
    IsSQTK K Y := by
  let _ := h.elementary
  let B := intersection A U g
  have hBV : B ≤ V := inf_le_left.trans d.subspace_mem.1
  have hn := h.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (B : Set G)) from
      ⟨B, hne, (IsElementaryAbelian.isPGroup 2 V).to_le hBV, rfl⟩)
  have hc : IsSQTK K (centralizer (B : Set G)) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (centralizer_le_normalizer (B : Set G)))).mp
      (hn.subgroup ((centralizer (B : Set G)).subgroupOf (normalizer (B : Set G))))
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hY.component.1)).mp
    (hc.subgroup (Y.subgroupOf (centralizer (B : Set G))))

/-- Exact earlier Theorems A and C classify Y/Z(Y); inheritance is discharged. -/
theorem quotient_model {K : GroupClass.{u}}
    (hA : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremA K D)
    (hC : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremC K D)
    {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (d : EscapeConfiguration M V U A L X g) (hne : intersection A U g ≠ ⊥)
    (hY : NormalComponentExtension U A X g Y) :
    ChapterA.Section02.IsTheoremCModel (Y ⧸ center Y) := by
  let _ := extension_quasisimple hY
  have hs := extension_sqtk h d hne hY
  let Q := Y ⧸ center Y
  let _ : IsSimpleGroup Q := IsQuasisimple.simple
  let _ : IsQuasisimple Q := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center Y)) (QuotientGroup.mk'_surjective (center Y))
  have htop : IsComponent Q (⊤ : Subgroup Q) :=
    ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have hsemi : ChapterA.Section02.IsSemisimple Q := top_unique (le_sSup htop)
  have hsec : ChapterA.Section02.IsSectionOf Q Y :=
    .of_surjective (QuotientGroup.mk' (center Y)) (QuotientGroup.mk'_surjective (center Y))
  exact hC Q inferInstance (Group.IsPerfect.not_isMulCommutative Q)
    ((hA Y).stronglyQuasithin_section hs.stronglyQuasithin hs.isKGroup hsec hsemi)
    (hs.isKGroup.quotient (center Y))

/-- Construct the actual linear equivalence once the central cover is removed. -/
theorem linearModelAction_of_quotient [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    (hm : ClassicalGroup.IsPSL (Y ⧸ center Y) 4 2 ∨
      ClassicalGroup.IsPSL (Y ⧸ center Y) 5 2)
    (hz : center Y = ⊥)
    (ho : ¬ actionImage A Y ≤ (MulAut.conj : Y →* MulAut Y).range) :
    LinearModelAction A Y := by
  let e : Y ⧸ center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans (QuotientGroup.quotientBot)
  exact ⟨hm.imp (fun ht => ht.of_mulEquiv e.symm) (fun ht => ht.of_mulEquiv e.symm),
    action_order_two d hY, ho⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
