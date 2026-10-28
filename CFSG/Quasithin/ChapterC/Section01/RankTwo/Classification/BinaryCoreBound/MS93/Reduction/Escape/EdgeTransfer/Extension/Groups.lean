module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Neighbors
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Quotient

/-!
# The literal neighboring extension group in MS93 (4.2)(i)

Put E = [Z_delta,Q_beta] Z_alpha and H = E D_alpha, where D_alpha is
`fixedCore`. The B-containment normalizes E under the local residual;
the edge kernel normalizes the displacement, so the whole local group
normalizes E and H. Both factors of E are commuting elementary groups.
Consequently the literal quotient H/D_alpha is elementary abelian.

The edge displacement has order at most four. Commutation with the local
two-kernel strictly reduces its order, giving a subgroup of order at most
two. This subgroup is normalized by the whole local group and hence is
central there. It follows that Q_alpha acts trivially on H/D_alpha.
No later edge containment, edge order, or distance-four structure is used.
The natural-module marking and the extension calculation are separate steps.

Adapted from the checked marked-extension proof in
`DistanceFour/Early/EdgeStructure/Containment/Transfer/SpanBound/Extension`.
The general construction uses the source and module data and b > 2.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), proof of (4.2)(i), printed p.882. The small-commutator argument is
the finite p-group commutator obstruction used in
`Theory.GroupTheory.PGroup.SmallElementaryNormal`; the order-two normalizer
argument also occurs in `Reduction.SectionThree.CriticalModules`.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Extension
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The neighboring displacement joined with the actual central Z-layer. -/
noncomputable def layer (a b d : Vertex R) : Subgroup (FreeAmalgam R) :=
  ⁅Z R d, Q R b⁆ ⊔ Z R a

/-- The literal source group [Z_delta,Q_beta] Z_alpha D_alpha. -/
noncomputable def carrier (a b d : Vertex R) : Subgroup (FreeAmalgam R) :=
  layer a b d ⊔ fixedCore R a

private theorem normalizes_sup {G : Type*} [Group G] (S A C : Subgroup G)
    (hA : S ≤ normalizer A) (hC : S ≤ normalizer C) :
    S ≤ normalizer (A ⊔ C : Subgroup G) :=
  (le_inf hA hC).trans (normalizer_inf_normalizer_le_normalizer_sup A C)

private theorem normalizes_commutator {G : Type*} [Group G] (S A C : Subgroup G)
    (hA : S ≤ normalizer A) (hC : S ≤ normalizer C) :
    S ≤ normalizer (⁅A,C⁆ : Subgroup G) := by
  intro s hs
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hs),
    mem_normalizer_iff_map_conj_eq.mp (hC hs)]

variable [Finite M] {L : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R} (hlarge : 2 < geometry.b R) (modules : ModuleFacts source geometry)

include hlarge modules

theorem layer_le_Q (a b d : Vertex R) (ha : color R a = false)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    layer a b d ≤ Q R a :=
  sup_le (neighbor_displacement_local hlarge a b d ha hB).1
    (by rw [← modules.X_eq_Z a ha]; exact omegaCenter_le _)

omit hlarge modules in
theorem displacement_normalized_kernel (a b d : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) :
    Q R a ≤ normalizer (⁅Z R d, Q R b⁆ : Subgroup (FreeAmalgam R)) := by
  have hb : color R b = true := by
    have h := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  exact (Q_le_adjacent_h R hb hab).trans (normalizer_commutator_ge_right _ _)

omit modules in
include source in
theorem layer_normalized (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    stabilizer R a ≤ normalizer (layer a b d : Set (FreeAmalgam R)) := by
  have hL : Ltilde R a ≤ normalizer (layer a b d : Set (FreeAmalgam R)) := by
    have hcomm : ⁅⁅Z R d,Q R b⁆,Ltilde R a⁆ ≤ Z R a :=
      (neighbor_displacement_local hlarge a b d ha hB).2
    rw [le_normalizer_iff]
    intro l hl x hx
    have hZ : Z R a ≤ layer a b d := le_sup_right
    have hX : ⁅Z R d,Q R b⁆ ≤ layer a b d := le_sup_left
    have hm : (layer a b d).map (MulAut.conj l).toMonoidHom ≤ layer a b d := by
      rw [layer, Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨y,hy,rfl⟩
        change l * y * l⁻¹ ∈ layer a b d
        have hc : ⁅l,y⁆ ∈ Z R a := hcomm (by
          rw [commutator_comm]; exact commutator_mem_commutator hl hy)
        rw [show l * y * l⁻¹ = ⁅l,y⁆ * y by simp [commutatorElement_def, mul_assoc]]
        exact (layer a b d).mul_mem (hZ hc) (hX hy)
      · rintro _ ⟨y,hy,rfl⟩
        exact hZ (le_normalizer_iff.mp ((Ltilde_le_stabilizer a).trans (Z_normalized R a)) l hl y hy)
    exact hm (mem_map_of_mem (MulAut.conj l).toMonoidHom hx)
  rw [← source.local_generation a ha]
  exact sup_le hL (normalizes_sup _ _ _
    (displacement_normalized_kernel a b d ha hab)
    ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a)))

theorem layer_elementary (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    IsElementaryAbelian 2 (layer a b d) := by
  have hd := neighbor_color a b d ha hab hdb
  let : IsElementaryAbelian 2 (Z R a) := by
    rw [← modules.X_eq_Z a ha]; exact omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z R d) := by
    rw [← modules.X_eq_Z d hd]; exact omegaCenter_elementary _
  let : IsElementaryAbelian 2 (⁅Z R d,Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    IsElementaryAbelian.of_le ((edge_commutator_le_natural hlarge modules d b hd hdb).trans (U_le_Z d))
  exact IsElementaryAbelian.sup_of_le_centralizer
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)).trans
      (centralizer_le (neighbor_displacement_local hlarge a b d ha hB).1))

theorem carrier_le_Q (a b d : Vertex R) (ha : color R a = false)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    carrier a b d ≤ Q R a := sup_le (layer_le_Q hlarge modules a b d ha hB) inf_le_left

omit modules in
include source in
theorem carrier_normalized (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    stabilizer R a ≤ normalizer (carrier a b d : Set (FreeAmalgam R)) :=
  normalizes_sup _ _ _ (layer_normalized (source := source) hlarge a b d ha hab hB)
    (fixedCore_normalized R a)

theorem denominator_normal (a b d : Vertex R) (ha : color R a = false)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ((fixedCore R a).subgroupOf (carrier a b d)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((carrier_le_Q hlarge modules a b d ha hB).trans (fun _ hx => hx.1)).trans
      (fixedCore_normalized R a))

theorem quotient_elementary (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    let := denominator_normal hlarge modules a b d ha hB
    IsElementaryAbelian 2 (carrier a b d ⧸ (fixedCore R a).subgroupOf (carrier a b d)) := by
  let := denominator_normal hlarge modules a b d ha hB
  let := layer_elementary hlarge modules a b d ha hab hdb hB
  have hn : layer a b d ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    ((layer_le_Q hlarge modules a b d ha hB).trans (fun _ hx => hx.1)).trans
      (fixedCore_normalized R a)
  let := normal_subgroupOf_of_le_normalizer hn
  let := normal_subgroupOf_sup_of_le_normalizer hn
  exact IsElementaryAbelian.of_surjective
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient (layer a b d) (fixedCore R a) hn).toMonoidHom
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient (layer a b d) (fixedCore R a) hn).surjective

omit hlarge modules [Finite M] in
private theorem small_commutator {G : Type*} [Group G]
    (P A : Subgroup G) [Finite P] (hP : IsPGroup 2 P)
    (hAP : A ≤ P) (hn : P ≤ normalizer A) (hA : Nat.card A ≤ 4) :
    Nat.card (⁅A,P⁆ : Subgroup G) ≤ 2 := by
  have hKA : ⁅A,P⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hn
  let : Finite A := Finite.of_injective (inclusion hAP) (inclusion_injective _)
  let : Finite (⁅A,P⁆ : Subgroup G) :=
    Finite.of_injective (inclusion hKA) (inclusion_injective _)
  by_cases hbot : A = ⊥
  · simp [hbot]
  have hne : ⁅A,P⁆ ≠ A := by
    intro heq
    let A₀ := A.subgroupOf P
    have hcomm : ⁅A₀, (⊤ : Subgroup P)⁆ = A₀ := by
      apply map_injective P.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hAP, ← MonoidHom.range_eq_map,
        range_subtype, heq]
    have hz : A₀ ≤ ⊥ := le_normal_of_quotient_isPGroup_of_eq_commutator
      A₀ ⊤ ⊥ (hP.to_quotient ⊥) hcomm
    have hh := congrArg (Subgroup.map P.subtype) (le_bot_iff.mp hz)
    rw [map_subgroupOf_eq_of_le hAP, Subgroup.map_bot] at hh
    exact hbot hh
  have hlt : Nat.card (⁅A,P⁆ : Subgroup G) < Nat.card A := by
    by_contra! h
    exact hne (eq_of_le_of_card_ge hKA h)
  rcases (hP.to_le (hKA.trans hAP)).card_eq_or_dvd with h | h <;> omega

omit hlarge modules [Finite M] in
private theorem normalizer_centralizes_small {G : Type*} [Group G]
    (D : Subgroup G) [Finite D] (hD : Nat.card D ≤ 2) :
    normalizer (D : Set G) ≤ centralizer (D : Set G) := by
  by_cases hsmall : Nat.card D ≤ 1
  · rw [eq_bot_of_card_le D hsmall]
    intro g _ x hx
    have hxone : x = 1 := hx
    simp [hxone]
  · have htwo : Nat.card D = 2 := by omega
    obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : D)).mp htwo
    intro g hg x hx
    by_cases hxone : x = 1
    · simp [hxone]
    let xD : D := ⟨x, hx⟩
    let yD : D := ⟨g * x * g⁻¹, (hg x).mp hx⟩
    have hyne : yD ≠ 1 := by
      intro hy
      apply hxone
      have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
      have hh := congrArg (fun a : G => g⁻¹ * a * g) hy'
      simpa [mul_assoc] using hh
    have heq : yD = xD := (hzuniq yD hyne).trans (hzuniq xD (by
      intro hx'; exact hxone (congrArg Subtype.val hx'))).symm
    have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
    have hh := congrArg (fun a : G => a * g) heq'
    simpa [mul_assoc] using hh.symm

omit modules in
theorem layer_commutator_eq (a b d : Vertex R) (ha : color R a = false)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅layer a b d,Q R a⁆ = ⁅⁅Z R d,Q R b⁆,Q R a⁆ := by
  have he := commutator_eq_of_centralizing_sup
    (show Z R a ⊔ ⁅Z R d,Q R b⁆ = layer a b d from sup_comm _ _)
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))
    ((neighbor_displacement_local hlarge a b d ha hB).1.trans (Q R a).le_normalizer)
  rw [commutator_comm (layer a b d), ← he, commutator_comm]

theorem layer_kernel_commutator_le_fixedCore (a b d : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅layer a b d,Q R a⁆ ≤ fixedCore R a := by
  let S := stabilizer R a
  let P := Q R a
  let E := layer a b d
  let K := ⁅E,P⁆
  have hP : P ≤ S := fun _ hx => hx.1
  let : Finite S := finite_stabilizer R a
  let : Finite P := Finite.of_injective (inclusion hP) (inclusion_injective _)
  have hK : K ≤ P := (commutator_mono (layer_le_Q hlarge modules a b d ha hB) le_rfl).trans
    (commutator_le_self P)
  let : Finite K := Finite.of_injective (inclusion hK) (inclusion_injective _)
  have hsmall : Nat.card K ≤ 2 := by
    change Nat.card (⁅layer a b d,Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 2
    rw [layer_commutator_eq hlarge a b d ha hB]
    exact small_commutator P _ (Q_isPGroup R source.two_group source.core_le a ha)
      (neighbor_displacement_local hlarge a b d ha hB).1
      (displacement_normalized_kernel a b d ha hab)
      (edge_displacement_card_le_four hlarge modules d b (neighbor_color a b d ha hab hdb) hdb)
  have hn : S ≤ normalizer K := normalizes_commutator S E P
    (layer_normalized (source := source) hlarge a b d ha hab hB) (Q_normalized R a)
  exact le_inf hK ((le_centralizer_iff.mp
    (hn.trans (normalizer_centralizes_small K hsmall))).trans
      (centralizer_le (Ltilde_le_stabilizer a)))

theorem carrier_kernel_commutator_le_fixedCore (a b d : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hB : ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅carrier a b d,Q R a⁆ ≤ fixedCore R a := by
  have hn : carrier a b d ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) :=
    ((carrier_le_Q hlarge modules a b d ha hB).trans (fun _ hx => hx.1)).trans
      (fixedCore_normalized R a)
  have hpre : carrier a b d ≤
      commutatorPreimage (carrier a b d) (Q R a) (fixedCore R a) :=
    sup_le (le_commutatorPreimage le_sup_left
      (layer_kernel_commutator_le_fixedCore hlarge modules a b d ha hab hdb hB))
      (le_commutatorPreimage le_sup_right
        (le_normalizer_iff_commutator_le_left.mp
          ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
            (fixedCore_normalized R a))))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hn)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.EdgeTransfer.Extension
