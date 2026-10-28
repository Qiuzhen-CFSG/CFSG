module
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.Representation.BinaryOffender.Homogeneous.Basic

/-!
# Fixed vectors in a span of irreducible component subspaces

Let B be a subgroup of K. A finite sum of Irr⁺ K-subspaces having no
B-fixed vectors also has no B-fixed vectors. Irreducible minimality makes
each new summand either contained in the preceding sum or disjoint from it;
in the disjoint case each coordinate of a fixed vector is fixed.
For normal K this applies to the full ambient orbit of a constituent.
No semisimplicity of the ambient module is assumed.

The odd PSL₃ source exclusion in Chapter 13 uses this on the actual Borel
residual. This is a general module argument supporting Aschbacher–Smith,
13.8.20(a), printed pp.954–955.
-/

set_option backward.isDefEq.respectTransparency false

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (K B : Subgroup G) (hBK : B ≤ K)

include hBK

private theorem fixed_sup_eq_bot
    {I J : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I)
    (hJ : K ≤ subspaceStabilizer ρ J)
    (hi : I ⊓ fixedSpace ρ B = ⊥) (hj : J ⊓ fixedSpace ρ B = ⊥) :
    (I ⊔ J) ⊓ fixedSpace ρ B = ⊥ := by
  have hstable : K ≤ subspaceStabilizer ρ (I ⊓ J) := by
    apply le_subspaceStabilizer
    intro k hk v hv
    exact ⟨(hI.choose hk v).2 hv.1, (hJ hk v).2 hv.2⟩
  rcases hI.eq_or_le_fixedSpace ρ hstable inf_le_left with he | hc
  · have hle : I ≤ J := he.ge.trans inf_le_right
    simpa only [sup_eq_right.mpr hle] using hj
  · have hd : Disjoint I J := by
      apply disjoint_iff.mpr
      apply le_bot_iff.mp
      rw [← hi]
      refine le_inf inf_le_left (hc.trans ?_)
      intro v hv b
      exact hv ⟨b,hBK b.property⟩
    apply (Submodule.eq_bot_iff _).mpr
    rintro v ⟨hv,hfix⟩
    obtain ⟨i,hiI,j,hjJ,rfl⟩ := Submodule.mem_sup.mp hv
    have hif : i ∈ fixedSpace ρ B := by
      intro b
      have he : ρ b i + ρ b j = i+j := by
        have hh := hfix b
        change ρ (b : G) (i+j) = i+j at hh
        simpa only [map_add] using hh
      have hz : ρ b i - i = 0 := by
        apply Submodule.disjoint_def.mp hd
        · exact I.sub_mem ((hI.choose (hBK b.property) i).2 hiI) hiI
        · have hh : ρ b i - i = j - ρ b j := by
            apply sub_eq_sub_iff_add_eq_add.mpr
            simpa only [add_comm j i] using he
          rw [hh]
          exact J.sub_mem hjJ ((hJ (hBK b.property) j).2 hjJ)
      exact sub_eq_zero.mp hz
    have hiz : i = 0 := by
      have hh : i ∈ I ⊓ fixedSpace ρ B := ⟨hiI,hif⟩
      simpa only [hi,Submodule.mem_bot] using hh
    have hjf : j ∈ fixedSpace ρ B := by
      intro b
      have hh := hfix b
      change ρ (b : G) (i+j) = i+j at hh
      change ρ (b : G) j = j
      simpa only [hiz,map_zero,zero_add] using hh
    have hjz : j = 0 := by
      have hh : j ∈ J ⊓ fixedSpace ρ B := ⟨hjJ,hjf⟩
      simpa only [hj,Submodule.mem_bot] using hh
    simp only [hiz,hjz,add_zero]

/-- A finite sum of Irr⁺ component subspaces with no B-fixed vectors has no
B-fixed vectors. No semisimplicity of the ambient module is assumed. -/
theorem finset_span_inf_fixedSpace_eq_bot {ι : Type*}
    (I : ι → Submodule (ZMod 2) V) (hI : ∀ i, IsIrrPlus ρ K (I i))
    (hz : ∀ i, I i ⊓ fixedSpace ρ B = ⊥) (s : Finset ι) :
    K ≤ subspaceStabilizer ρ (s.sup I) ∧ (s.sup I) ⊓ fixedSpace ρ B = ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor
      · apply le_subspaceStabilizer
        intro k hk v hv
        simp only [Finset.sup_empty,Submodule.mem_bot] at hv ⊢
        rw [hv,map_zero]
      · simp
  | @insert i s hi ih =>
      simp only [Finset.sup_insert]
      exact ⟨subspaceStabilizer_sup ρ (hI i).choose ih.1,
        fixed_sup_eq_bot ρ K B hBK (hI i) ih.1 (hz i) ih.2⟩

/-- If no conjugate of an Irr⁺ component subspace has B-fixed vectors,
its literal full ambient orbit span has none. -/
theorem orbitSpan_inf_fixedSpace_eq_bot [Finite G] [K.Normal]
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hz : ∀ g : G, I.map (ρ g) ⊓ fixedSpace ρ B = ⊥) :
    orbitSpan ρ ⊤ I ⊓ fixedSpace ρ B = ⊥ := by
  classical
  let := Fintype.ofFinite G
  have he : (Finset.univ : Finset G).sup (fun g => I.map (ρ g)) = orbitSpan ρ ⊤ I := by
    rw [Finset.sup_eq_iSup]
    simp only [Finset.mem_univ,iSup_pos]
    apply le_antisymm
    · exact iSup_le fun g => le_iSup (fun g : (⊤ : Subgroup G) => I.map (ρ g)) ⟨g,mem_top g⟩
    · exact iSup_le fun g => le_iSup (fun g : G => I.map (ρ g)) g
  rw [← he]
  exact (finset_span_inf_fixedSpace_eq_bot ρ K B hBK (fun g : G => I.map (ρ g))
    (fun g => hI.map_normalizer ρ (by rw [normalizer_eq_top]; trivial)) hz Finset.univ).2
end Representation.BinaryOffender.Homogeneous
