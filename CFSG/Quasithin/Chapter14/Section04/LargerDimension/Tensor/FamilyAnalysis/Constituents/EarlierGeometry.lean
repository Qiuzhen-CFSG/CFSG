module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Images

/-!
# Earlier source inputs and assembly for the tensor constituent geometry

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 14.3.10, printed p.993; 14.4.2(5), p.1006; and the first proof
paragraph of 14.4.10, p.1010. The earlier local facts are 12.8.8–13,
printed pp.851–855, and U = O₂(H) is 14.4.7.

The central layer is literally C_U(V₂); its conjugate uses the convention
Wᵍ = g⁻¹ W g; the intersection is literally W ∩ Wᵍ. EarlierGeometry
records precise earlier local premises, including relative normality of
the image of Wᵍ in the point centralizer. It does not replace the genuine
ambient Hypothesis 14.3.10, which remains with the source assembly owner.
It assumes neither an invariant constituent nor a moved-plane containment.
In particular, normalization of V₂ is used to prove fixation of its image.

SelectedConstituent is the output contract for the independent constituent
construction, not an existence assertion. It preserves the chosen element,
the actual displacement space, its cubic-translate complement, and an
equivariant identification with the original constituent. Once constructed,
its complement splits the first moved plane. The final theorem combines the
still-explicit intersection calculation with the actual earlier commutator
bound and the extraspecial central-kernel lift to prove X₁ ∈ Y.
-/

@[expose] public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G]

/-- The literal subgroup W = C_U(P). -/
def centralLayer (U P : Subgroup G) : Subgroup G := U ⊓ centralizer (P : Set G)

/-- Right conjugation: Wᵍ = g⁻¹ W g. -/
def conjugateLayer (U P : Subgroup G) (g : G) : Subgroup G :=
  (centralLayer U P).map (MulAut.conj g⁻¹).toMonoidHom

/-- The literal source intersection E = W ∩ Wᵍ. -/
def intersectionLayer (U P : Subgroup G) (g : G) : Subgroup G :=
  centralLayer U P ⊓ conjugateLayer U P g

namespace CaseFiveCoordinates
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U : Subgroup G} (c : CaseFiveCoordinates hAD (V := V) H U)

/-- The literal star image followed by the published actor coordinates. -/
noncomputable abbrev actorImage (A : Subgroup G) : Subgroup (Three × D) :=
  (star H A).map c.actor.toMonoidHom

/-- Containment passes through the same two actor quotient maps. -/
theorem actorImage_mono {A B : Subgroup G} (h : A ≤ B) : c.actorImage A ≤ c.actorImage B :=
  map_mono (map_mono (subgroupOf_mono H h))

/-- Pointwise centralizer of the actual quotient image of P. -/
noncomputable def pointCentralizer (P : Subgroup G) : Subgroup (Three × D) :=
  subspaceKernel (sourceTensorAction c.constituent) (c.image P) ⊤

/-- The binary commutator form, identified by its values on actual lifts. Over F₂ the zero test determines every value, so this permits no unrelated form. -/
structure CanonicalForm where
  form : LinearMap.BilinForm (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V)
  commutes_iff : ∀ u v : U,
    form (c.quotientMap u).toAdd (c.quotientMap v).toAdd = 0 ↔ Commute u v

/-- Earlier 12.8/14.3 premises and the rank-three Wᵍ image from 14.4.2. -/
structure EarlierGeometry (T P : Subgroup G) (g : G) : Prop where
  sylow : ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = T
  U_le_T : U ≤ T
  U_eq_core : U = twoCore H
  point_le_U : P ≤ U
  center_le_point : center U ≤ P.subgroupOf U
  point_rank : Module.finrank (ZMod 2) (c.image P) = 1
  T_normalizes_point : T ≤ normalizer (P : Set G)
  conjugator_normalizes : g ∈ normalizer (P : Set G)
  conjugator_outside : g ∉ H
  conjugate_le_T : conjugateLayer U P g ≤ T
  point_le_intersection : P ≤ intersectionLayer U P g
  conjugate_elementary : IsElementaryAbelian 2 (star H (conjugateLayer U P g))
  conjugate_card : Nat.card (star H (conjugateLayer U P g)) = 8
  conjugate_normal : ((c.actorImage (conjugateLayer U P g)).subgroupOf
    (c.pointCentralizer P)).Normal
  commutator_le : ⁅conjugateLayer U P g, centralLayer U P⁆ ≤ intersectionLayer U P g

/-- A nonzero invariant submodule with no proper nonzero invariant submodule. -/
def IsIrreducibleFor (A : Subgroup G)
    (M : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V)) : Prop :=
  M ≠ ⊥ ∧ c.actorImage A ≤ subspaceStabilizer (sourceTensorAction c.constituent) M ∧
    ∀ N : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V),
      N ≤ M → c.actorImage A ≤ subspaceStabilizer (sourceTensorAction c.constituent) N →
        N = ⊥ ∨ N = M

/-- Output to be constructed for 14.4.10(2), with its chosen complement. No theorem below asserts existence of this data from the earlier premises. -/
structure SelectedConstituent (T P : Subgroup G) (g : G) where
  element : coreQuotient H
  element_mem : element ∈ star H (conjugateLayer U P g)
  element_ne_one : element ≠ 1
  element_centralizes : element ∈ centralizer (star H (component H) : Set (coreQuotient H))
  firstSpace : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V)
  secondSpace : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V)
  first_eq_range : firstSpace = LinearMap.range
    (sourceTensorAction c.constituent (c.actor element) - LinearMap.id)
  second_eq_translate : secondSpace = firstSpace.map
    (sourceTensorAction c.constituent (cubicActor D))
  isCompl : IsCompl firstSpace secondSpace
  first_irreducible : c.IsIrreducibleFor (component H) firstSpace
  constituentEquiv : V ≃ₗ[ZMod 2] firstSpace
  constituent_equivariant : ∀ (a : AltFive) (v : V),
    (constituentEquiv (c.constituent (inclusion hAD a) v) :
      BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V) =
    sourceTensorAction c.constituent (1, inclusion hAD a)
      (constituentEquiv v : BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V)
  second_invariant : c.actorImage (component H) ≤
    subspaceStabilizer (sourceTensorAction c.constituent) secondSpace
  T_invariant : c.actorImage T ≤ subspaceStabilizer (sourceTensorAction c.constituent) firstSpace
  point_le_fixed : c.image P ≤ fixedSpace (sourceTensorAction c.constituent) (c.actorImage T)
  fixed_le_first : fixedSpace (sourceTensorAction c.constituent) (c.actorImage T) ≤ firstSpace
  unique : ∀ M : Submodule (ZMod 2) (BinaryPermutation.core (Fin 3) ⊗[ZMod 2] V),
    c.IsIrreducibleFor (component H) M →
      c.actorImage T ≤ subspaceStabilizer (sourceTensorAction c.constituent) M → M = firstSpace

/-- The actual Sylow witness supplies T ≤ H. -/
theorem EarlierGeometry.T_le_H {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g) :
    T ≤ H := by
  obtain ⟨S, hS⟩ := h.sylow
  rw [← hS]
  exact map_subtype_le _

/-- Application of the canonical form to the literal source W. -/
theorem EarlierGeometry.centralLayer_image {T P : Subgroup G} {g : G}
    (h : c.EarlierGeometry T P g) (B : c.CanonicalForm) :
    c.image (centralLayer U P) = (c.image P).orthogonalBilin B.form :=
  c.image_centralizer P h.point_le_U B.form B.commutes_iff

/-- The source normalization and quotient rank imply Ṽ₂ ≤ C_Ũ(T). -/
theorem EarlierGeometry.point_fixed {T P : Subgroup G} {g : G}
    (h : c.EarlierGeometry T P g) :
    c.image P ≤ fixedSpace (sourceTensorAction c.constituent) (c.actorImage T) :=
  c.point_fixed_of_normalizes h.T_le_H h.T_normalizes_point h.point_rank

/-- The literal 12.8.11(1) bound, with the actual conjugate Wᵍ. -/
theorem EarlierGeometry.source_bound {T P : Subgroup G} {g : G}
    (h : c.EarlierGeometry T P g) :
    subspaceCommutator (sourceTensorAction c.constituent) (c.image (centralLayer U P))
      (c.actorImage (conjugateLayer U P g)) ≤ c.image (intersectionLayer U P g) := by
  apply c.source_commutator_bound inf_le_left (h.conjugate_le_T.trans h.T_le_H)
  rw [commutator_comm]
  exact h.commutator_le

/-- The actual first moved subgroup has order eight under the earlier local inputs. -/
theorem EarlierGeometry.first_order_eight [Finite G] [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g) :
    Nat.card (movedSpace P (first H)) = 8 :=
  c.first_movedSpace_card_eight h.T_le_H h.U_le_T h.point_le_U h.center_le_point h.point_rank

/-- The chosen cubic-translate complement gives the source plane decomposition. -/
theorem SelectedConstituent.first_image_split [Finite G]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (s : c.SelectedConstituent T P g) :
    c.image (movedSpace P (first H)) = c.image P ⊔
      (c.image (movedSpace P (first H)) ⊓ s.secondSpace) := by
  have hne : c.image P ≠ ⊥ := by
    intro he
    have hd := h.point_rank
    rw [he, finrank_bot] at hd
    omega
  obtain ⟨v, hv, hv0⟩ := (c.image P).ne_bot_iff.mp hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one h.point_rank hv hv0
  rw [c.first_image_eq_cubicPlane h.point_le_U v hspan]
  have hvp : v ∈ cubicPlane c.constituent v := Submodule.subset_span (Or.inl rfl)
  have hrp : sourceTensorAction c.constituent (cubicActor D) v ∈
      cubicPlane c.constituent v := Submodule.subset_span (Or.inr rfl)
  have hrs : sourceTensorAction c.constituent (cubicActor D) v ∈ s.secondSpace := by
    rw [s.second_eq_translate]
    exact Submodule.mem_map.mpr ⟨v, s.fixed_le_first (s.point_le_fixed hv), rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro w hw
    rcases (show w = v ∨ w = sourceTensorAction c.constituent (cubicActor D) v from hw)
      with he | he
    · rw [he]
      exact Submodule.mem_sup_left hv
    · rw [he]
      exact Submodule.mem_sup_right ⟨hrp, hrs⟩
  · apply sup_le _ inf_le_left
    rw [hspan]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvp)

/-- Conditional assembly: the source intersection calculation gives X₁ ∈ Y. Its premise must be proved in both constituent alternatives before claiming 14.4.10. -/
theorem EarlierGeometry.first_mem_Y_of_intersection [Finite G] [IsExtraspecial 2 U]
    {T P : Subgroup G} {g : G} (h : c.EarlierGeometry T P g)
    (s : c.SelectedConstituent T P g)
    (hcalc : c.image (movedSpace P (first H)) ⊓ s.secondSpace ≤
      subspaceCommutator (sourceTensorAction c.constituent)
        (c.image (centralLayer U P) ⊓ s.secondSpace)
        (c.actorImage (conjugateLayer U P g) ⊓ c.actorImage (component H))) :
    first H ∈ YFamily H T P (intersectionLayer U P g) := by
  apply c.first_mem_Y_of_image_le h.T_le_H h.U_le_T h.point_le_U h.center_le_point
    (h.center_le_point.trans (subgroupOf_mono U h.point_le_intersection)) h.point_rank
  rw [SelectedConstituent.first_image_split c h s]
  apply sup_le (c.image_mono h.point_le_intersection)
  apply hcalc.trans
  apply le_trans _ h.source_bound
  apply Submodule.span_le.mpr
  rintro v ⟨a, ha, w, hw, rfl⟩
  exact Submodule.subset_span ⟨a, ha.1, w, hw.1, rfl⟩

end CaseFiveCoordinates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
