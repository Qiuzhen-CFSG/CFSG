module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TwoElementConjugates
/-!
# The characteristic elementary orbit in Campbell's Theorem A reduction

If every Aut(S)-image of V lies in O₂(H), the paired span bounds put each
image of F in J(O₂(H)), so each centralizes F. Applying an inverse
automorphism shows all Aut(S)-images of F commute. Their actual orbit span
inside S is therefore elementary abelian, characteristic, nontrivial and
contained in the ambient two-core. Nontriviality comes from an original
natural point moved by S, with no additional seed witness.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.7.1,
printed p.33, in the Aut(S) corollary used by C.1.18. The remaining
Theorem A commutator containment is not assumed or asserted here.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.automorphism_F_centralizes_F (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    automorphismImage S a (Campbell.F H) ≤ centralizer (Campbell.F H : Set H) := by
  have hYR : automorphismImage S a (Campbell.F H) ≤ Campbell.J (pCore 2 H) := by
    have hh := h.original_span_core_frattini (h.precomp_equiv a.symm) hB
      (show ((Campbell.V H).comap (S.subtype.comp a.symm.toMonoidHom)).map S.subtype ≤ pCore 2 H by
        rw [←comap_comap,comap_equiv_eq_map_symm']; exact hV)
    dsimp only at hh
    rw [←comap_comap,comap_equiv_eq_map_symm'] at hh
    exact (le_conjugateSpanBy _ _).trans hh.1
  apply hYR.trans
  apply le_centralizer_iff.mpr
  exact fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2

/-- The literal Aut(S)-orbit span of Campbell's F inside S. -/
@[expose] noncomputable def campbellAutomorphismOrbit : Subgroup S :=
  closure {x : S | ∃ a : MulAut S, ∃ r : S, (r:H) ∈ Campbell.F H ∧ a r=x}

theorem InLocalClass.automorphism_orbit_elementary (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S)
    (hV : ∀ a : MulAut S, automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    IsElementaryAbelian 2 (campbellAutomorphismOrbit S) := by
  let C := {x : S | ∃ a : MulAut S, ∃ r : S, (r:H) ∈ Campbell.F H ∧ a r=x}
  have hcomm : ∀ x∈C, ∀ y∈C, x*y=y*x := by
    rintro x ⟨a,r,hr,rfl⟩ y ⟨b,s,hs,rfl⟩
    apply b.symm.injective
    simp only [map_mul,b.symm_apply_apply]
    apply Subtype.ext
    have hc := h.automorphism_F_centralizes_F S hB (a.trans b.symm) (hV _)
    have hmem : ((a.trans b.symm) r:H) ∈ automorphismImage S (a.trans b.symm) (Campbell.F H) :=
      mem_map_of_mem S.subtype (mem_map_of_mem (a.trans b.symm).toMonoidHom hr)
    exact (hc hmem s hs).symm
  let : IsMulCommutative (closure C) := isMulCommutative_closure hcomm
  change IsElementaryAbelian 2 (closure C)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨a,r,hr,rfl⟩
  let : IsElementaryAbelian 2 (Campbell.F H) := omegaOneCenterAmbient_elementaryAbelian _
  have hr2 : r^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (r:H) hr)
  rw [←map_pow,hr2,map_one]

omit [Finite H] in
theorem campbellAutomorphismOrbit_characteristic : (campbellAutomorphismOrbit S).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro b
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro x ⟨a,r,hr,rfl⟩
    exact subset_closure ⟨a.trans b,r,hr,rfl⟩
  · apply (closure_le _).mpr
    rintro x ⟨a,r,hr,rfl⟩
    refine ⟨b.symm (a r),subset_closure ⟨a.trans b.symm,r,hr,rfl⟩,?_⟩
    exact b.apply_symm_apply _


theorem InLocalClass.automorphism_orbit_ne_bot (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) : campbellAutomorphismOrbit S ≠ ⊥ := by
  obtain ⟨v,hv,hvn⟩ := h.exists_campbell_nonfixed_point hB
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  let v' : S := ⟨v,Campbell.V_le_pCore.trans hQS hv⟩
  have hvOrbit : v' ∈ campbellAutomorphismOrbit S :=
    subset_closure ⟨MulEquiv.refl S,v',Campbell.V_le_F hv,rfl⟩
  intro he
  have hv1 : v'=1 := mem_bot.mp (he ▸ hvOrbit)
  apply hvn
  have hvone : v=1 := congrArg Subtype.val hv1
  rw [hvone]
  exact one_mem _

theorem InLocalClass.automorphism_orbit_le_core (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S)
    (hV : ∀ a : MulAut S, automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    (campbellAutomorphismOrbit S).map S.subtype ≤ pCore 2 H := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro x ⟨a,r,hr,rfl⟩
  have hs := h.sylow_automorphism_span S hB a (hV a)
  apply hs.1
  apply le_conjugateSpanBy
  exact mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom hr)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
