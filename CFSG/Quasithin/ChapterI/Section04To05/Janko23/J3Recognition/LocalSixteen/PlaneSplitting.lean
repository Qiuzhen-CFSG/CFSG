module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneAction
public import Theory.GroupTheory.GaschutzElementaryPair
public import Theory.GroupTheory.SplitExtensionCoordinates.Marked
public import Theory.GroupAction.IrreducibleTwoCoreKernel

/-!
# Splitting the full normalizers of the elementary sixteen-groups

The two elementary planes generate R and contain its center, so each is
normal in R and has an elementary complement there. The full plane
normalizer has order 2880, making the index of R equal to 45. Gaschütz's
coprime-index theorem therefore splits the whole normalizer over the
original plane. The resulting order-180 complement is marked by its actual
conjugation action, and the semidirect-product equivalence fixes every
embedded plane element.

Fusion transitivity also proves irreducibility of the literal automizer.
Its two-core is trivial, so the original plane is exactly the two-core of
its full ambient normalizer. These are inputs to the five-coset action in
the source; identifying the order-180 automizer as natural GL₂(4) remains
a separate obligation.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(5a), pp.257–258;
Aschbacher–Smith A.1.39 for Gaschütz's theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.HyperbolicRecognition
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D)

/-- Every elementary sixteen-group in R contains its center E. -/
theorem E_le_plane (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R) : P.E ≤ A := by
  obtain ⟨d⟩ := Geometry.Coordinates.rootEquiv P
  rcases (P.elementary_sixteen_iff d A hAR).mp ⟨inferInstance,hA⟩ with rfl | rfl
  · rw [←P.planes_inf d]; exact inf_le_left
  · rw [←P.planes_inf d]; exact inf_le_right

/-- The root group normalizes each of its elementary planes separately. -/
theorem R_le_plane_normalizer (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R) : P.R ≤ normalizer (A : Set G) := by
  let : IsElementaryAbelian 2 (P.R ⧸ P.E.subgroupOf P.R) := P.root_quotient_elementary
  have hd : _root_.commutator P.R ≤ P.E.subgroupOf P.R :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro x hx y hy
  exact P.E_le_plane A hA hAR (hd (commutator_mem_commutator
    (show (⟨x,hx⟩ : P.R) ∈ ⊤ from mem_top _) (show (⟨y,hAR hy⟩ : P.R) ∈ ⊤ from mem_top _)))

/-- The actual root group has odd index 45 in the full plane normalizer. -/
theorem root_index_in_plane_normalizer (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    P.R.relIndex (normalizer (A : Set G)) = 45 := by
  have hc : Nat.card (P.R.subgroupOf (normalizer (A : Set G))) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe (P.R_le_plane_normalizer A hA hAR)).toEquiv).trans P.R_card
  have hh := (P.R.subgroupOf (normalizer (A : Set G))).card_mul_index
  rw [hc,P.plane_normalizer_card hclass A hA hAR] at hh
  change 64 * P.R.relIndex (normalizer (A : Set G)) = 2880 at hh
  omega

private theorem exists_elementary_supplement (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ B : Subgroup G, IsElementaryAbelian 2 B ∧ A ⊔ B = P.R := by
  obtain ⟨d⟩ := Geometry.Coordinates.rootEquiv P
  rcases (P.elementary_sixteen_iff d A hAR).mp ⟨inferInstance,hA⟩ with rfl | rfl
  · exact ⟨P.A₂ d,inferInstance,P.planes_sup d⟩
  · exact ⟨P.A₁ d,inferInstance,(sup_comm _ _).trans (P.planes_sup d)⟩

/-- The whole ambient normalizer splits over its original plane. -/
theorem plane_normalizer_splits (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ C : Subgroup (normalizer (A : Set G)),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' C := by
  let N := normalizer (A : Set G)
  let V := A.subgroupOf N
  let U := P.R.subgroupOf N
  have hRN := P.R_le_plane_normalizer A hA hAR
  have hVU : V ≤ U := fun _ hx => hAR hx
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf le_normalizer
  apply exists_complement_of_coprime_overgroup V U hVU
  · have hV : Nat.card V = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ N from le_normalizer)).toEquiv).trans hA
    have hU : U.index = 45 := P.root_index_in_plane_normalizer hclass A hA hAR
    rw [hV,hU]
    decide
  · obtain ⟨B,hB,hAB⟩ := P.exists_elementary_supplement A hA hAR
    let : IsElementaryAbelian 2 B := hB
    have hBR : B ≤ P.R := le_sup_right.trans_eq hAB
    let W := B.subgroupOf N
    have hWU : W ≤ U := fun _ hx => hBR hx
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf (hBR.trans hRN)
    let : IsElementaryAbelian 2 (W.subgroupOf U) := IsElementaryAbelian.subgroupOf hWU
    apply exists_complement_of_sup_elementary (p := 2) (V.subgroupOf U) (W.subgroupOf U)
    apply map_injective U.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVU,map_subgroupOf_eq_of_le hWU,
      ←MonoidHom.range_eq_map,range_subtype]
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show A ≤ N from le_normalizer),
      map_subgroupOf_eq_of_le (hBR.trans hRN),map_subgroupOf_eq_of_le hRN,hAB]

/-- Every such complement has the exact automizer order. -/
theorem plane_complement_card (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (C : Subgroup (normalizer (A : Set G)))
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C) : Nat.card C = 180 := by
  have hV : Nat.card (A.subgroupOf (normalizer (A : Set G))) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : A ≤ normalizer (A : Set G))).toEquiv).trans hA
  have hh := hC.card_mul_card
  rw [hV,P.plane_normalizer_card hclass A hA hAR] at hh
  omega

/-- Kernel-marked coordinates for the whole normalizer with its literal faithful action. -/
theorem plane_normalizer_semidirect (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ f : normalizer (A : Set G) ≃* A ⋊[A.normalizerMonoidHom.range.subtype]
        A.normalizerMonoidHom.range,
      ∀ a : A, f (inclusion le_normalizer a) = SemidirectProduct.inl a := by
  let N := normalizer (A : Set G)
  let V := A.subgroupOf N
  let eA := (QuotientGroup.quotientMulEquivOfEq
    (P.plane_normalizer_action_kernel A hA hAR).symm).trans
      (QuotientGroup.quotientKerEquivRange A.normalizerMonoidHom)
  let eV : V ≃* A := subgroupOfEquivOfLe le_normalizer
  obtain ⟨C,hC⟩ := P.plane_normalizer_splits hclass A hA hAR
  obtain ⟨f,hf,_⟩ := exists_marked_semidirect_equiv_of_split_coordinates V C hC eA eV
    A.normalizerMonoidHom.range.subtype (by intro n a; rfl)
  exact ⟨f,fun a => hf (eV.symm a)⟩

/-- The complement is identified with the actual automizer, retaining conjugation. -/
theorem plane_normalizer_marked_complement (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ (C : Subgroup (normalizer (A : Set G)))
      (f : C ≃* A.normalizerMonoidHom.range),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
      Nat.card C = 180 ∧
      ∀ c : C, (f c : MulAut A) = A.normalizerMonoidHom c := by
  obtain ⟨C,hC⟩ := P.plane_normalizer_splits hclass A hA hAR
  let f := A.normalizerMonoidHom.rangeRestrict.comp C.subtype
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro c hc
    apply mem_bot.mpr
    apply Subtype.ext
    apply hC.disjoint.le_bot
    refine ⟨?_,c.property⟩
    rw [←P.plane_normalizer_action_kernel A hA hAR]
    exact congrArg Subtype.val hc
  have hs : Function.Surjective f :=
    (Nat.bijective_iff_injective_and_card f).mpr
      ⟨hi,(P.plane_complement_card hclass A hA hAR C hC).trans
        (P.plane_normalizer_action_card hclass A hA hAR).symm⟩ |>.2
  exact ⟨C,MulEquiv.ofBijective f ⟨hi,hs⟩,hC,
    P.plane_complement_card hclass A hA hAR C hC,fun _ => rfl⟩

include P in
/-- The literal faithful action is transitive on nonidentity plane elements. -/
theorem plane_automizer_transitive (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (x y : A) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ b : A.normalizerMonoidHom.range, b • x = y := by
  obtain ⟨n,hn,hxy⟩ := P.elementary_sixteen_normalizer_transitive hclass A hA x y
    x.property y.property (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
  exact ⟨⟨A.normalizerMonoidHom ⟨n,hn⟩,⟨⟨n,hn⟩,rfl⟩⟩,Subtype.ext hxy⟩

include P in
/-- Every subgroup invariant under the actual normalizer action is zero or the whole plane. -/
theorem plane_automizer_irreducible (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (W : Subgroup A)
    (hW : ∀ b : A.normalizerMonoidHom.range, ∀ a : A, a ∈ W → b • a ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨⟨x,hx⟩,hx1⟩ := ne_bot_iff_exists_ne_one.mp hb
    apply top_unique
    intro y _
    by_cases hy : y = 1
    · exact hy ▸ W.one_mem
    · obtain ⟨b,hb⟩ := P.plane_automizer_transitive hclass A hA x y (fun h => hx1 (Subtype.ext h)) hy
      exact hb ▸ hW b x hx

include P in
/-- There is no normal two-subgroup in the actual automizer. -/
theorem plane_automizer_twoCore (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) :
    pCore 2 A.normalizerMonoidHom.range = ⊥ := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hA]; decide)
  exact irreducible_range_two_core_eq_bot _ (P.plane_automizer_irreducible hclass A hA)

/-- The plane is precisely the two-core of its whole ambient normalizer. -/
theorem plane_normalizer_twoCore (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    pCore 2 (normalizer (A : Set G)) = A.subgroupOf (normalizer (A : Set G)) := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hA]; decide)
  apply le_antisymm
  · rw [←P.plane_normalizer_action_kernel A hA hAR]
    exact irreducible_range_core_le_ker A.normalizerMonoidHom
      (P.plane_automizer_irreducible hclass A hA)
  · let : IsElementaryAbelian 2 (A.subgroupOf (normalizer (A : Set G))) :=
      IsElementaryAbelian.subgroupOf le_normalizer
    exact le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 _⟩

end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
