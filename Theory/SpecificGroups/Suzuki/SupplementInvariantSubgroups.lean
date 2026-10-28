module
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting.Coordinates
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.Frattini.PGroup

/-!
# Subgroups invariant under a Suzuki normalizer supplement

Let P be a Sylow two-subgroup of Sz(q), and let C supplement P in its
full normalizer. A subgroup D of P normalized by C is central or equals P.
In standard root coordinates, a noncentral element has nonzero first
coordinate. Factor each split-torus element through P and C. Conjugation
by P is trivial on the first-coordinate quotient, so the C-invariant
image of D contains every field element. The kernel is the derived
subgroup and lies in the Frattini subgroup; hence D is all of P.

Sylow conjugacy transports the dichotomy through the supplied model
isomorphism. In particular a proper invariant subgroup has order at most
q. No oddness or disjointness assumption on the supplement is needed.
The full-edge application is CommutingThreeProfile.SuzukiComplementTransitivity.

Source: Huppert--Blackburn III, XI.3.1--3.3; the complement-action step of
DGS85, Groups and Graphs, (12.8), printed p.186.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups
open SchurCover.Family

private theorem root_eq_of_supplement_invariant
    {m : ℕ} (hm : 0 < m) (D C : Subgroup (SuzukiMatrixGroup m))
    (hD : D ≤ SuzukiRootSubgroup m)
    (hC : SuzukiRootSubgroup m ⊔ C = SuzukiBorelSubgroup m)
    (hn : C ≤ normalizer (D : Set (SuzukiMatrixGroup m)))
    (hne : ¬ D ≤ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype) :
    D = SuzukiRootSubgroup m := by
  let R := SuzukiRootSubgroup m
  let J := D.subgroupOf R
  let f := rootCoordinate m hm
  have hCR : C ≤ normalizer (R : Set (SuzukiMatrixGroup m)) := by
    rw [suzukiRootSubgroup_normalizer m hm]
    exact hC ▸ le_sup_right
  have hnot : ¬ J ≤ f.ker := by
    intro hh
    apply hne
    intro d hd
    have hk := hh (show (⟨d,hD hd⟩ : R) ∈ J from hd)
    rw [rootCoordinate_ker m hm,root_commutator_eq_center m hm] at hk
    exact mem_map_of_mem R.subtype hk
  obtain ⟨d,hd,hdf⟩ := Set.not_subset.mp hnot
  obtain ⟨a,b,hda⟩ := rootPoint_surjective m d
  have ha : a ≠ 0 := by
    intro he
    apply hdf
    change f d = 1
    rw [hda]
    exact congrArg Multiplicative.ofAdd he
  have him : J.map f = ⊤ := by
    apply top_unique
    intro z _
    by_cases hz : z = 1
    · exact hz ▸ (J.map f).one_mem
    let u : (Field m)ˣ := Units.mk0 (z.toAdd / a) (div_ne_zero
      (fun he => hz (congrArg Multiplicative.ofAdd he)) ha)
    have hu : (u : Field m) * a = z.toAdd := div_mul_cancel₀ _ ha
    have ht : torusPoint m hm u ∈ (R : Set (SuzukiMatrixGroup m)) * (C : Set (SuzukiMatrixGroup m)) := by
      rw [←coe_mul_of_right_le_normalizer_left R C hCR,hC,suzukiBorelSubgroup_eq_sup]
      exact (show SuzukiSplitTorus m ≤ SuzukiRootSubgroup m ⊔ SuzukiSplitTorus m from le_sup_right)
        (torusPoint_mem m hm u)
    obtain ⟨p,hp,c,hc,he⟩ := ht
    have hcd : c * (d : SuzukiMatrixGroup m) * c⁻¹ ∈ D :=
      (mem_normalizer_iff.mp (hn hc) d).mp hd
    let v : R := ⟨c * (d : SuzukiMatrixGroup m) * c⁻¹,hD hcd⟩
    have hconj : (⟨p,hp⟩ : R) * v * (⟨p,hp⟩ : R)⁻¹ =
        rootPoint m ((u : Field m)*a) ((u : Field m)*suzukiTits m u*b) := by
      apply Subtype.ext
      have ht := torusPoint_conj m hm u a b
      rw [←he,←hda] at ht
      simpa only [v,Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,mul_assoc] using ht
    have hv : f v = z := by
      have hh := congrArg f hconj
      rw [map_mul,map_mul,map_inv,mul_comm (f ⟨p,hp⟩),mul_assoc,
        mul_inv_cancel,mul_one] at hh
      change f v = Multiplicative.ofAdd ((u : Field m) * a) at hh
      simpa only [hu,ofAdd_toAdd] using hh
    exact ⟨v,hcd,hv⟩
  have hsup : J ⊔ f.ker = ⊤ := by
    have he := congrArg (Subgroup.comap f) him
    simpa only [comap_map_eq,comap_top] using he
  have hJ : J = ⊤ := by
    let : Fact (IsPGroup 2 R) := ⟨suzukiRootSubgroup_isPGroup m hm⟩
    apply frattini_nongenerating_of_isPGroup (p := 2) J
    apply top_unique
    rw [←hsup]
    apply sup_le_sup_left
    rw [rootCoordinate_ker]
    exact commutator_le_frattini_of_isPGroup (p := 2)
  apply le_antisymm hD
  intro r hr
  exact show (⟨r,hr⟩ : R) ∈ J from hJ ▸ mem_top _

/-- A subgroup of a Suzuki Sylow invariant under a full normalizer supplement
is either central or the whole Sylow. -/
theorem suzuki_supplement_invariant_dichotomy
    {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 0 < m)
    (e : X ≃* SuzukiMatrixGroup m) (P : Sylow 2 X) (D C : Subgroup X)
    (hD : D ≤ P) (hC : (P : Subgroup X) ⊔ C = normalizer (P : Set X))
    (hn : C ≤ normalizer (D : Set X)) :
    D ≤ (center P).map (P : Subgroup X).subtype ∨ D = (P : Subgroup X) := by
  by_cases hz : D ≤ (center P).map (P : Subgroup X).subtype
  · exact Or.inl hz
  right
  obtain ⟨f,hP,hB⟩ := suzukiSylow_aligned_equiv hm e P
  have hP' : (P : Subgroup X).map f.symm.toMonoidHom = SuzukiRootSubgroup m := by
    rw [←hP,map_map]
    simp
  have hB' : (normalizer (P : Set X)).map f.symm.toMonoidHom = SuzukiBorelSubgroup m := by
    rw [←hB,map_map]
    simp
  have hD' := map_mono (f := f.symm.toMonoidHom) hD
  rw [hP'] at hD'
  have hC' := congrArg (Subgroup.map f.symm.toMonoidHom) hC
  rw [Subgroup.map_sup,hP',hB'] at hC'
  have hn' := map_mono (f := f.symm.toMonoidHom) hn
  rw [map_equiv_normalizer_eq] at hn'
  have hz' : ¬ D.map f.symm.toMonoidHom ≤
      (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype := by
    rw [←hP',←map_embeddedCenter _ _ f.symm.injective]
    exact fun hh => hz ((map_le_map_iff_of_injective f.symm.injective).mp hh)
  apply map_injective (f := f.symm.toMonoidHom) f.symm.injective
  rw [hP']
  exact root_eq_of_supplement_invariant hm _ _ hD' hC' hn' hz'

/-- A proper invariant subgroup has order at most q. -/
theorem suzuki_supplement_invariant_card_or_full
    {X : Type*} [Group X] [Finite X] {m : ℕ} (hm : 0 < m)
    (e : X ≃* SuzukiMatrixGroup m) (P : Sylow 2 X) (D C : Subgroup X)
    (hD : D ≤ P) (hC : (P : Subgroup X) ⊔ C = normalizer (P : Set X))
    (hn : C ≤ normalizer (D : Set X)) :
    Nat.card D ≤ 2^(2*m+1) ∨ D = (P : Subgroup X) := by
  rcases suzuki_supplement_invariant_dichotomy hm e P D C hD hC hn with hz | he
  · left
    have hh := Nat.card_le_card_of_injective (inclusion hz) (inclusion_injective hz)
    rw [card_map_of_injective (P : Subgroup X).subtype_injective,
      (suzukiSylow_borel_structure hm e P).1] at hh
    exact hh
  · exact Or.inr he

end BenderSuzuki.MatrixGroups
