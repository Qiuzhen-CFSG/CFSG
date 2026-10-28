module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComplementAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ResidualReduction

/-!
# The embedding step in the contrary Sylow configuration

The input records the placed contrary overgroup and the actual action on the
two source factors. Movement generates the whole X inside H. The other source
factor lies outside N_G(X), which proves relative nonnormality of X in H.
The full S₃ × S₃ quotient then constructs the intrinsic Ξ input and the D₈
complement automizer. Applying the universal corrected local 1.3.4 excludes
its normal and cyclic-automizer alternatives.

The linear-three and M₁₁ exclusions, the full automorphism-group assertion for
the binary-linear case, and the reverse residual containment remain separate
obligations. In particular the intermediate alternatives here retain those
unresolved models. The normal closure is taken inside H, and its containment
in O^{3′}(H) uses the actual three-group quotient of X.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.3.4,
printed pp.509–511, and the second paragraph of 15.4.20, pp.1163–1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u
variable {G : Type u} [Group G]

/-- The genuine corrected local implication, universally quantified before
specializing to the contrary configuration. Its proof belongs to §1.3. -/
def LocalEmbeddingTheorem (κ : GroupClass.{u}) : Prop :=
  ∀ (A : Type u) [Group A] [Finite A] (p : ℕ) (T X P H : Subgroup A),
    Chapter1.XiEmbedding.LocalInput p T X P H → IsSQTK κ H →
      Chapter1.IsSylowIn 2 T H → Chapter1.XiEmbedding.Conclusion p T X P H

/-- Raw source data in the moved-X orientation. No Ξ membership, embedding
alternative, normal-closure identity, or final Sylow conclusion is included. -/
structure PlacedX (d : Source.Geometry G) (i j : Bool) (H U : Subgroup G) where
  overgroup : H ∈ Chapter1.HOver G (d.I i j : Set G)
  sylow : Sylow 2 H
  sylow_image : (sylow : Subgroup H).map H.subtype = U
  lower : d.T₀ < U
  upper : U < (d.T : Subgroup G)
  lower_index : d.T₀.relIndex U = 2
  upper_index : U.relIndex (d.T : Subgroup G) = 2
  maximal : ∀ J ∈ Chapter1.HOver G (d.I i j : Set G), ∀ Q : Sylow 2 J,
    Nat.card ((Q : Subgroup J).map J.subtype) ≤ Nat.card U
  core_sylow : Chapter1.IsSylowIn 2 U (normalizer (H.pCoreIn 2 : Set G))
  T_normalizes : (d.T : Subgroup G) ≤ d.M₁
  baumann_le : ChapterB.baumann (d.T : Subgroup G) ≤ U
  permutes : ∀ u ∈ U, ∃ σ : Equiv.Perm Bool,
    ∀ k, (d.X k).map (MulAut.conj u).toMonoidHom = d.X (σ k)
  moves : ¬ U ≤ normalizer (d.X i : Set G)
  outside : ¬ d.Y j ≤ d.M₁
  perfect : IsPPerfect 2 d.wholeX
  core_nontrivial : d.wholeX.pCoreIn 2 ≠ ⊥
  quotient : (d.wholeX ⧸ pCore 2 d.wholeX) ≃* Multiplicative (ZMod 3 × ZMod 3)
  product : (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G) →*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  product_surjective : Function.Surjective product
  product_kernel : product.ker =
    pCore 2 (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G)
  first_image : ((d.X false).subgroupOf
    (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G))).map product =
      (alternatingGroup (Fin 3)).prod ⊥
  second_image : ((d.X true).subgroupOf
    (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G))).map product =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3))
  first_perfect : IsPPerfect 2 (d.X i)
  other_perfect : IsPPerfect 2 (d.Y j)
  first_quotient_card : Nat.card (d.X i ⧸ pCore 2 (d.X i)) = 3
  other_quotient_card : Nat.card (d.Y j ⧸ pCore 2 (d.Y j)) = 3

variable {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}

/-- The moving factor generates the whole source X in the actual overgroup. -/
theorem PlacedX.whole_le (h : PlacedX d i j H U) : d.wholeX ≤ H := by
  exact (moved_factor_generates_whole d.X i
    (h.sylow_image ▸ map_subtype_le (h.sylow : Subgroup H))
    ((d.X_le_I i j).trans h.overgroup.2) h.permutes h.moves).2

/-- The outside Y-factor rules out relative normality of X in H. -/
theorem PlacedX.not_normal (h : PlacedX d i j H U) :
    ¬ (d.wholeX.subgroupOf H).Normal := by
  intro hn
  have hHN : H ≤ d.M₁ := (normal_subgroupOf_iff_le_normalizer h.whole_le).mp hn
  exact h.outside ((d.Y_le_I i j).trans (h.overgroup.2.trans hHN))

private theorem PlacedX.permutes_set (h : PlacedX d i j H U) :
    ∀ u ∈ U, ∀ V ∈ ({d.X false, d.X true} : Set (Subgroup G)),
      V.map (MulAut.conj u).toMonoidHom ∈ ({d.X false, d.X true} : Set (Subgroup G)) := by
  intro u hu V hV
  obtain ⟨σ, hσ⟩ := h.permutes u hu
  have hm (k : Bool) : (d.X k).map (MulAut.conj u).toMonoidHom ∈
      ({d.X false, d.X true} : Set (Subgroup G)) := by
    rw [hσ k]
    cases σ k <;> simp
  rcases Set.mem_insert_iff.mp hV with rfl | hV
  · exact hm false
  · exact Set.mem_singleton_iff.mp hV ▸ hm true

/-- Construct both the local 1.3.4 input and its noncyclic D₈ automizer
from the full source action. The Sylow hypothesis is retained explicitly. -/
theorem PlacedX.embedding_input [Finite G] {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    IsSQTK κ H ∧
      Chapter1.XiEmbedding.LocalInput 3 U d.wholeX
        ((P : Subgroup d.wholeX).map d.wholeX.subtype) H ∧
      Chapter1.IsSylowIn 2 U H ∧
      Nonempty (Chapter1.XiEmbedding.automizer U
        ((P : Subgroup d.wholeX).map d.wholeX.subtype) ≃* DihedralGroup 4) := by
  have hU : IsPGroup 2 U := h.sylow_image ▸ h.sylow.isPGroup'.map H.subtype
  have hn : U ≤ normalizer (d.wholeX : Set G) := h.upper.le.trans h.T_normalizes
  have hXi := (contrary_Xi_from_full_product d.wholeX
    (ChapterB.baumann (d.T : Subgroup G)) U hU h.baumann_le hn h.perfect
    h.core_nontrivial h.quotient d.X rfl h.product h.product_surjective h.product_kernel
    h.first_image h.second_image h.permutes_set i h.moves).1
  obtain ⟨hSQ, hlocal, hSylow⟩ := contrary_local_embedding_input hG h.overgroup.1
    h.whole_le h.sylow h.sylow_image hXi h.quotient P
  have hD := contrary_dihedral_from_full_product d.wholeX
    (ChapterB.baumann (d.T : Subgroup G)) U hU h.baumann_le hn h.quotient d.X rfl
    h.product h.product_surjective h.product_kernel h.first_image h.second_image
    h.permutes_set i h.moves
  exact ⟨hSQ, hlocal, hSylow,
    contrary_complement_automizer_dihedral hXi
      (hSylow.restrict le_sup_right hlocal.overgroup) h.quotient P hD⟩

/-- A D₈ complement automizer excludes the symplectic alternative. This
intermediate sieve deliberately retains the unresolved L₃(3) and M₁₁ cases. -/
theorem alternatives_of_dihedral {T P L : Subgroup G}
    (ha : Chapter1.XiEmbedding.Alternatives 3 T P L)
    (hD : Nonempty (Chapter1.XiEmbedding.automizer T P ≃* DihedralGroup 4)) :
    Nonempty (P ≃* Chapter1.XiEmbedding.Plane 3) ∧
      ((Chapter1.XiEmbedding.SwappedFactors T P L ∧
          Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient L)) ∨
        (T ≤ normalizer L ∧
          (Chapter1.XiEmbedding.LinearThreeModel 3 (Chapter1.XiQuotient L) ∨
            Chapter1.XiEmbedding.ExceptionalModel (Chapter1.XiQuotient L)))) := by
  obtain ⟨e⟩ := hD
  have hnc : ¬ IsCyclic (Chapter1.XiEmbedding.automizer T P) := by
    intro hc
    let _ := hc
    exact DihedralGroup.not_isCyclic (by decide : 4 ≠ 1)
      (isCyclic_of_surjective e e.surjective)
  refine ⟨ha.1, ?_⟩
  rcases ha.2 with hs | ⟨hn, hm⟩
  · exact Or.inl hs
  · refine Or.inr ⟨hn, ?_⟩
    rcases hm with hl | ⟨_, hc⟩ | ⟨_, he⟩
    · exact Or.inl hl
    · exact (hnc hc).elim
    · exact Or.inr he

/-- Apply the universal corrected embedding theorem only after constructing
its Sylow input, and eliminate its normal and symplectic alternatives. -/
theorem PlacedX.component_alternatives [Finite G] {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (embedding : LocalEmbeddingTheorem κ) (h : PlacedX d i j H U)
    (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    ∃ L : Subgroup G, L ∈ Chapter1.cComponentsIn H ∧
      IsQuasisimple (Chapter1.XiQuotient L) ∧ d.wholeX ≤ componentOrbit L U ∧
      Nonempty (P₀ ≃* Chapter1.XiEmbedding.Plane 3) ∧
      Nonempty (Chapter1.XiEmbedding.automizer U P₀ ≃* DihedralGroup 4) ∧
      ((Chapter1.XiEmbedding.SwappedFactors U P₀ L ∧
          Chapter1.XiEmbedding.SwappedModel 3 (Chapter1.XiQuotient L)) ∨
        (U ≤ normalizer L ∧
          (Chapter1.XiEmbedding.LinearThreeModel 3 (Chapter1.XiQuotient L) ∨
            Chapter1.XiEmbedding.ExceptionalModel (Chapter1.XiQuotient L)))) := by
  obtain ⟨hsq, hlocal, hsylow, hD⟩ := h.embedding_input hG P
  rcases embedding G 3 U d.wholeX _ H hlocal hsq hsylow with hn | ⟨L, hL, hq, hX, ha⟩
  · exact (h.not_normal hn).elim
  · obtain ⟨he, hs⟩ := alternatives_of_dihedral ha hD
    exact ⟨L, hL, hq, hX, he, hD, hs⟩

/-- The ambient image of the H-normal closure; this is not ambient G-normality. -/
def normalClosureIn (X H : Subgroup G) : Subgroup G :=
  (normalClosure (X.subgroupOf H : Set H)).map H.subtype

/-- The relative normal closure contains its generating subgroup. -/
theorem le_normalClosureIn {X H : Subgroup G} (hXH : X ≤ H) :
    X ≤ normalClosureIn X H := by
  intro x hx
  exact ⟨⟨x, hXH hx⟩, le_normalClosure (show (⟨x, hXH hx⟩ : H) ∈
    X.subgroupOf H from hx), rfl⟩

/-- Relative normal closure stays in the specified overgroup. -/
theorem normalClosureIn_le_overgroup (X H : Subgroup G) : normalClosureIn X H ≤ H :=
  map_subtype_le _

/-- Normality is relative to H. -/
theorem normalClosureIn_normal (X H : Subgroup G) :
    ((normalClosureIn X H).subgroupOf H).Normal := by
  change (((normalClosure (X.subgroupOf H : Set H)).map H.subtype).comap H.subtype).Normal
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

/-- The normal closure is contained in every relatively normal overgroup of X. -/
theorem normalClosureIn_le {X H N : Subgroup G} (hXN : X ≤ N) (hNH : N ≤ H)
    (hn : (N.subgroupOf H).Normal) : normalClosureIn X H ≤ N := by
  let _ := hn
  exact (map_mono (f := H.subtype) (normalClosure_le_normal
    (show (X.subgroupOf H : Set H) ⊆ N.subgroupOf H from fun _ hx => hXN hx))).trans_eq
      (map_subgroupOf_eq_of_le hNH)

/-- The constructed normal closure lies in the genuine prime-to-three residual.
The reverse containment is the remaining A.3.18/1.2.2 step. -/
theorem PlacedX.normalClosure_le_residual [Finite G] (h : PlacedX d i j H U) :
    normalClosureIn d.wholeX H ≤ (primeToResidual 3 H).map H.subtype := by
  have hX := twoPerfect_three_quotient_le_primeToResidual h.whole_le h.perfect
    ((order_nine_quotient_structure h.quotient).1.isPGroup)
  apply normalClosureIn_le hX (map_subtype_le _)
  change (((primeToResidual 3 H).map H.subtype).comap H.subtype).Normal
  rw [comap_map_eq_self_of_injective H.subtype_injective]
  infer_instance

/-- In the invariant simple-quotient branch, a subgroup with nontrivial
image normally generates the component. Perfectness removes the possible
two-group quotient left after using simplicity. -/
theorem normalClosureIn_eq_of_simple_twoCoreQuotient [Finite G]
    {X L H : Subgroup G} (hXL : X ≤ L) (hLH : L ≤ H)
    (hn : (L.subgroupOf H).Normal) (hp : IsPPerfect 2 L)
    (hs : IsSimpleGroup (L ⧸ pCore 2 L)) (hne : ¬ X ≤ L.pCoreIn 2) :
    normalClosureIn X H = L := by
  let _ := hs
  let N := normalClosureIn X H
  have hNH : N ≤ H := normalClosureIn_le_overgroup X H
  have hNL : N ≤ L := normalClosureIn_le hXL hLH hn
  have hXN : X ≤ N := le_normalClosureIn (hXL.trans hLH)
  have hHN : H ≤ normalizer (N : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hNH).mp (normalClosureIn_normal X H)
  let D := N.subgroupOf L
  let _ : D.Normal := (normal_subgroupOf_iff_le_normalizer hNL).mpr (hLH.trans hHN)
  let q := QuotientGroup.mk' (pCore 2 L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hnormal : (D.map q).Normal := (inferInstance : D.Normal).map q hq
  have ht : D.map q = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map q) hnormal with hb | ht
    · exfalso
      apply hne
      have hD : D ≤ pCore 2 L := by
        simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hb
      intro x hx
      exact ⟨⟨x, hXL hx⟩, hD (hXN hx), rfl⟩
    · exact ht
  have hgen : D ⊔ pCore 2 L = ⊤ := by
    have he := congrArg (Subgroup.comap q) ht
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
  have hD : D = ⊤ := hp D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (pCore 2 L) pCore_isPGroup hgen)
  have he := congrArg (Subgroup.map L.subtype) hD
  simpa only [D, map_subgroupOf_eq_of_le hNL, ← MonoidHom.range_eq_map,
    range_subtype] using he

/-- The order-nine quotient prevents the whole source X from lying in
any two-group, in particular in the intrinsic two-core of a component. -/
theorem PlacedX.not_le_two_group [Finite G] (h : PlacedX d i j H U)
    {B : Subgroup G} (hB : IsPGroup 2 B) : ¬ d.wholeX ≤ B := by
  intro hXB
  have ht : IsPGroup 2 (d.wholeX ⧸ pCore 2 d.wholeX) :=
    (hB.to_le hXB).of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := ht.exists_card_dvd_pow
  have hcard := (order_nine_quotient_structure h.quotient).2.1
  rw [hcard] at hn
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow
    ((by decide : 3 ∣ 3 ^ 2).trans hn))

/-- Apply simple-quotient normal generation without an additional
nontrivial-image premise: the source order-nine quotient supplies it. -/
theorem PlacedX.normalClosure_eq_component [Finite G] (h : PlacedX d i j H U)
    {L : Subgroup G} (hXL : d.wholeX ≤ L) (hLH : L ≤ H)
    (hn : (L.subgroupOf H).Normal) (hp : IsPPerfect 2 L)
    (hs : IsSimpleGroup (L ⧸ pCore 2 L)) : normalClosureIn d.wholeX H = L :=
  normalClosureIn_eq_of_simple_twoCoreQuotient hXL hLH hn hp hs
    (h.not_le_two_group (isPGroup_pCoreIn 2 L))

/-- In the exchanged alternative, the selected component has an actual
nontrivial three-subgroup in its image in H/O₂(H). This verifies the prime
divisibility premise of 1.2.2(a), rather than inferring it from a family name. -/
theorem swapped_three_dvd_quotient_image [Finite G]
    {T X P H L : Subgroup G} (h : Chapter1.XiEmbedding.LocalInput 3 T X P H)
    (hs : Chapter1.XiEmbedding.SwappedFactors T P L) :
    3 ∣ Nat.card ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) := by
  let A := P ⊓ L
  have hPH : P ≤ H := (le_sup_right.trans h.complement.le).trans
    (le_sup_left.trans h.overgroup)
  have hAH : A ≤ H := inf_le_left.trans hPH
  have hAb : A ≠ ⊥ := by
    intro hb
    obtain ⟨_, t, _, _, hgen, _, _⟩ := hs
    have hPb : P = ⊥ := by simpa only [A, hb, Subgroup.conjBy, Subgroup.map_bot, bot_sup_eq] using hgen
    have hc := h.complement_not_cyclic
    rw [hPb] at hc
    exact hc inferInstance
  have hA3 : IsPGroup 3 A := h.odd_complement.isPGroup.to_le inf_le_left
  let R := A.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hd : Disjoint (pCore 2 H) R :=
    pCore_isPGroup.disjoint_of_coprime hA3.comap_subtype (by decide : Nat.Coprime 2 3)
  have hRb : R.map q ≠ ⊥ := by
    intro hb
    have hRcore : R ≤ pCore 2 H := by
      simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hb
    have hR : R = ⊥ := le_bot_iff.mp (fun x hx => hd.le_bot ⟨hRcore hx, hx⟩)
    have he := congrArg (Subgroup.map H.subtype) hR
    exact hAb (by simpa only [R, map_subgroupOf_eq_of_le hAH, Subgroup.map_bot] using he)
  have hp : 3 ∣ Nat.card (R.map q) :=
    (hA3.comap_subtype.map q).card_eq_or_dvd.resolve_left
      (fun hc => hRb (Subgroup.card_eq_one.mp hc))
  exact hp.trans (card_dvd_of_le (map_mono (f := q)
    (show R ≤ L.subgroupOf H from fun _ hx => hx.2)))

/-- A moved component attains an available two-conjugate bound. All
normalizers and conjugates in this calculation are intrinsic to H. -/
theorem two_conjugates_of_moved [Finite G] {T H L : Subgroup G}
    (hTH : T ≤ H) (hLH : L ≤ H) (hmove : ¬ T ≤ normalizer L)
    (hbound : (normalizer (L.subgroupOf H : Set H)).index ≤ 2) :
    (Set.range fun x : H => (L.subgroupOf H).map (MulAut.conj x).toMonoidHom).ncard = 2 := by
  rw [ncard_conjugates_eq_index_normalizer]
  have hne : (normalizer (L.subgroupOf H : Set H)).index ≠ 1 := by
    intro he
    have hn : (L.subgroupOf H).Normal :=
      normalizer_eq_top_iff.mp (index_eq_one.mp he)
    exact hmove (hTH.trans ((normal_subgroupOf_iff_le_normalizer hLH).mp hn))
  have hpos := (normalizer (L.subgroupOf H : Set H)).index_ne_zero_of_finite
  omega

/-- The literal residual replacement preserves the amalgam, its Sylow group,
all further eligible overgroup Sylow assertions, and the new core normalizer.
Identification of this residual with the X-normal closure is still required
before using this as the `KU` replacement in the source proof. -/
theorem PlacedX.residual_replacement [Finite G] (h : PlacedX d i j H U) :
    let D := (primeToResidual 3 H).map H.subtype ⊔ U
    D ∈ Chapter1.HOver G (d.I i j : Set G) ∧
      Chapter1.IsSylowIn 2 U D ∧
      (∀ J ∈ Chapter1.HOver G (D : Set G), Chapter1.IsSylowIn 2 U J) ∧
      Chapter1.IsSylowIn 2 U (normalizer (D.pCoreIn 2 : Set G)) := by
  exact threeResidual_sylow_replacement h.overgroup.1 h.sylow h.sylow_image h.lower.le
    ((d.X_le_I i j).trans h.overgroup.2) ((d.Y_le_I i j).trans h.overgroup.2)
    h.first_perfect h.other_perfect h.first_quotient_card h.other_quotient_card h.maximal

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
