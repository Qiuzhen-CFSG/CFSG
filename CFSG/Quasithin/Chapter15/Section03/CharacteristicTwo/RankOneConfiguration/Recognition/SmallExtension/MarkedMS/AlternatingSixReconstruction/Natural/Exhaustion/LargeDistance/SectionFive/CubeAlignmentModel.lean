module
public import Theory.Representation.BinaryPermutationSixCover
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreCrossing
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives

/-!
# Alignment or full displacement control in a marked three-pair group

Fix the critical transposition on either six-letter cover. Its fixed-kernel
commutator with a subgroup of the same three-pair group is either contained
in the critical line plus the full fixed central attachment, or, together
with the critical line, contains the whole-cover commutator.

In canonical augmentation-core coordinates the critical transposition is
(45). The fixed-kernel displacement is determined by the displacement of
the single test word {0,2}. Its four possible values are 0, {0,1}, {2,3},
and {0,1,2,3}. The last is the critical pair word plus the constant word.
If a nonaligned test displacement occurs, a checked coordinate certificate
expresses every full displacement using that test word, the actor's test
word and the critical pair word. Linearity extends the certificate to every
vector and taking spans gives the two alternatives.

A surjective equivariant core map transports the result to either cover.
Nonvanishing on the critical pair word lifts the exact fixed kernel; the
constant word maps into the full fixed space. A single pair relabeling and
conjugation retain the given transposition and three-pair subgroup. The
literal replacement-cover application is in `CubeAlignmentControl`.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.7)--(5.8), printed pp.866--867,919--920. This is the
alignment/control calculation, not a proof that the selected source line
satisfies the alignment alternative.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel
local notation "ρ" => coreRepresentation (Fin 6)
private def delta (g : S) : Full (Fin 6) →ₗ[ZMod 2] C :=
  ((representation (Fin 6) g)-LinearMap.id).codRestrict (core (Fin 6)) (by
    intro v
    change augmentation (Fin 6) (representation (Fin 6) g v-v)=0
    rw [map_sub,augmentation_permute,sub_self])
private def test : C := pairWord 0 2
private def dword (j : Fin 8) : C := ρ (initialWords 3 j) test-test

private theorem dword_cases : ∀ j : Fin 8,
    dword j=0 ∨ dword j=pairWord 0 1 ∨ dword j=pairWord 2 3 ∨
      dword j=pairWord 0 1+pairWord 2 3 := by
  decide +kernel

private theorem fixed_displacement_certificate :
    ∀ (v : Full (Fin 6)) (j : Fin 8), (∑ i, v i)=0 → v 4=v 5 →
      delta (initialWords 3 j) v = (v 0+v 1) • dword j := by
  decide +kernel

private theorem control_certificate : ∀ (j k : Fin 8) (i : Fin 6),
    (dword j=pairWord 0 1 ∨ dword j=pairWord 2 3) →
    ∃ a b c : ZMod 2,
      delta (initialWords 3 k) (Pi.single i 1) =
        a • dword j+b • dword k+c • pairWord 4 5 := by
  decide +kernel

private theorem critical_mem : pairWord 4 5 ∈ subspaceCommutator ρ ⊤ (zpowers swap45) := by
  rw [swap45_moved]
  exact Submodule.subset_span (Set.mem_singleton _)

private theorem dword_mem (P : Subgroup S) (j : Fin 8) (hj : initialWords 3 j ∈ P) :
    dword j ∈ subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) P := by
  apply Submodule.subset_span
  refine ⟨initialWords 3 j,hj,test,?_,rfl⟩
  apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
  decide +kernel

/-- Canonical augmentation-core alignment/control dichotomy. -/
private theorem core_canonical_dichotomy (P : Subgroup S) (hP : P ≤ D 6) :
    subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) P ≤
      subspaceCommutator ρ ⊤ (zpowers swap45) ⊔ Submodule.span (ZMod 2) {oneWord} ∨
    subspaceCommutator ρ ⊤ P ≤
      subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) P ⊔
        subspaceCommutator ρ ⊤ (zpowers swap45) := by
  let H := subspaceCommutator ρ (fixedSpace ρ (zpowers swap45)) P
  let T := subspaceCommutator ρ ⊤ (zpowers swap45) ⊔ Submodule.span (ZMod 2) {oneWord}
  by_cases h : ∀ j : Fin 8, initialWords 3 j ∈ P → dword j ∈ T
  · left
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).mp (hP hg)
    have hfix := (mem_fixedSpace_zpowers_iff _ _ _).mp hv
    have h45 : v.val 4=v.val 5 := by
      have hh := congrArg (fun w : C => w.val 5) hfix
      exact hh
    change delta (initialWords 3 j) v.val ∈ T
    rw [fixed_displacement_certificate v.val j v.property h45]
    exact T.smul_mem _ (h j hg)
  · right
    push Not at h
    obtain ⟨j,hj,hnj⟩ := h
    have hjcase : dword j=pairWord 0 1 ∨ dword j=pairWord 2 3 := by
      rcases dword_cases j with he | he | he | he
      · exact False.elim (hnj (he ▸ T.zero_mem))
      · exact Or.inl he
      · exact Or.inr he
      · apply False.elim
        apply hnj
        rw [he,show pairWord 0 1+pairWord 2 3=pairWord 4 5+oneWord by decide +kernel]
        exact T.add_mem (show _ ∈ T from Submodule.mem_sup_left critical_mem)
          (show _ ∈ T from Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _)))
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    obtain ⟨k,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).mp (hP hg)
    let W := H ⊔ subspaceCommutator ρ ⊤ (zpowers swap45)
    have hc (i : Fin 6) : delta (initialWords 3 k) (Pi.single i 1) ∈ W := by
      obtain ⟨a,b,c,he⟩ := control_certificate j k i hjcase
      rw [he]
      exact W.add_mem (W.add_mem
        (W.smul_mem a (show _ ∈ W from Submodule.mem_sup_left (dword_mem P j hj)))
        (W.smul_mem b (show _ ∈ W from Submodule.mem_sup_left (dword_mem P k hg))))
        (W.smul_mem c (show _ ∈ W from Submodule.mem_sup_right critical_mem))
    have hv : v.val = ∑ i : Fin 6, v.val i • Pi.single i 1 := by
      ext i
      simp [Pi.single_apply]
    change delta (initialWords 3 k) v.val ∈ W
    rw [hv,map_sum]
    exact W.sum_mem (fun i _ => by rw [map_smul]; exact W.smul_mem _ (hc i))

/-- The canonical dichotomy survives either cover and its central kernel. -/
private theorem mapped_canonical_dichotomy
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y) (f : C →ₗ[ZMod 2] Y)
    (hf : Function.Surjective f) (he : ∀ g v, f (ρ g v)=σ g (f v))
    (hn : f (pairWord 4 5) ≠ 0) (P : Subgroup S) (hP : P ≤ D 6) :
    subspaceCommutator σ (fixedSpace σ (zpowers swap45)) P ≤
      subspaceCommutator σ ⊤ (zpowers swap45) ⊔ fixedSpace σ ⊤ ∨
    subspaceCommutator σ ⊤ P ≤
      subspaceCommutator σ (fixedSpace σ (zpowers swap45)) P ⊔
        subspaceCommutator σ ⊤ (zpowers swap45) := by
  have hF : (fixedSpace ρ (zpowers swap45)).map f = fixedSpace σ (zpowers swap45) := by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      rw [←he,(mem_fixedSpace_zpowers_iff _ _ _).mp hv]
    · intro w hw
      obtain ⟨v,rfl⟩ := hf w
      refine ⟨v,?_,rfl⟩
      have hh : (v.val 4+v.val 5) • f (pairWord 4 5)=0 := by
        rw [←map_smul,←swap45_displacement,map_sub,he,
          (mem_fixedSpace_zpowers_iff _ _ _).mp hw,sub_self]
      have hz : v.val 4+v.val 5=0 := (smul_eq_zero.mp hh).resolve_right hn
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      apply sub_eq_zero.mp
      rw [swap45_displacement,hz,zero_smul]
  have hmap (I : Submodule (ZMod 2) C) (B : Subgroup S) :
      (subspaceCommutator ρ I B).map f = subspaceCommutator σ (I.map f) B := by
    have hh := subspaceCommutator_map_embedding σ ρ (MonoidHom.id S) f
      (fun g v => (he g v).symm) B I
    simpa only [map_id] using hh.symm
  have hfT : (⊤ : Submodule (ZMod 2) C).map f = ⊤ := by
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr hf]
  have hcentral : (Submodule.span (ZMod 2) {oneWord}).map f ≤ fixedSpace σ ⊤ := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl,rfl⟩
    intro g
    have hh : ρ g.val oneWord=oneWord := by rfl
    change σ g.val (f oneWord)=f oneWord
    rw [←he,hh]
  rcases core_canonical_dichotomy P hP with h | h
  · left
    have hm := Submodule.map_mono (f := f) h
    rw [Submodule.map_sup,hmap,hmap,hF,hfT] at hm
    exact hm.trans (sup_le_sup_left hcentral _)
  · right
    have hm := Submodule.map_mono (f := f) h
    rwa [Submodule.map_sup,hmap,hmap,hmap,hF,hfT] at hm

private def relabel (i : Fin 3) : S :=
  ![Equiv.swap 0 4 * Equiv.swap 1 5, Equiv.swap 2 4 * Equiv.swap 3 5,1] i

private theorem relabel_cube (i : Fin 3) :
    (D 6).map (MulAut.conj (relabel i)).toMonoidHom = D 6 := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g,hg,rfl⟩
    obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).mp hg
    have cert : ∀ (i : Fin 3) (j : Fin 8), ∃ k : Fin 8,
        (MulAut.conj (relabel i)) (initialWords 3 j)=initialWords 3 k := by decide +kernel
    obtain ⟨k,hk⟩ := cert i j
    exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨k,hk.symm⟩
  · rw [card_map_of_injective (MulAut.conj (relabel i)).injective]

private theorem marked_cube (u t : S)
    (ht : t ∈ (D 6).map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap) :
    ∃ w : S, (D 6).map (MulAut.conj w).toMonoidHom =
      (D 6).map (MulAut.conj u).toMonoidHom ∧ (MulAut.conj w) swap45=t := by
  obtain ⟨a,ha,hat⟩ := ht
  have hsA : a.IsSwap := by
    have hc : IsConj a t := isConj_iff.mpr ⟨u,hat⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hc).trans (Equiv.Perm.isSwap_iff_cycleType.mp hs))
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) a).mp ha
  have cert : ∀ j : Fin 8, (initialWords 3 j).cycleType={2} →
      ∃ i : Fin 3, initialWords 3 j=pairSwap 6 i := by decide +kernel
  obtain ⟨i,he⟩ := cert j (Equiv.Perm.isSwap_iff_cycleType.mp hsA)
  have hrel : (MulAut.conj (relabel i)) swap45=pairSwap 6 i := by
    have hh : ∀ i : Fin 3, (MulAut.conj (relabel i)) swap45=pairSwap 6 i := by decide +kernel
    exact hh i
  refine ⟨u*relabel i,?_,?_⟩
  · have hcomp : (MulAut.conj u).toMonoidHom.comp (MulAut.conj (relabel i)).toMonoidHom =
        (MulAut.conj (u*relabel i)).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change u*(relabel i*g*(relabel i)⁻¹)*u⁻¹=(u*relabel i)*g*(u*relabel i)⁻¹
      group
    rw [←hcomp,←map_map,relabel_cube]
  · have hh : (MulAut.conj (u*relabel i)) swap45=
        (MulAut.conj u) ((MulAut.conj (relabel i)) swap45) := by
      change (u*relabel i)*swap45*(u*relabel i)⁻¹=u*(relabel i*swap45*(relabel i)⁻¹)*u⁻¹
      group
    rw [hh,hrel,←he]
    exact hat

/-- Alignment/control on either actual six-letter cover in any marked cube. -/
theorem model_dichotomy {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore σ (MonoidHom.id S))
    (u t : S) (P : Subgroup S)
    (hP : P ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    (ht : t ∈ (D 6).map (MulAut.conj u).toMonoidHom) (hs : t.IsSwap) :
    subspaceCommutator σ (fixedSpace σ (zpowers t)) P ≤
      subspaceCommutator σ ⊤ (zpowers t) ⊔ fixedSpace σ ⊤ ∨
    subspaceCommutator σ ⊤ P ≤
      subspaceCommutator σ (fixedSpace σ (zpowers t)) P ⊔
        subspaceCommutator σ ⊤ (zpowers t) := by
  have hex : ∃ f : C →ₗ[ZMod 2] Y, Function.Surjective f ∧
      (∀ g v, f (ρ g v)=σ g (f v)) ∧ f (pairWord 4 5) ≠ 0 := by
    rcases hm with ⟨E,hE⟩ | ⟨E,hE⟩
    · let f := E.symm.toLinearMap.comp (coreToNatural (Fin 6))
      refine ⟨f,E.symm.surjective.comp coreToNatural_surjective,?_,?_⟩
      · intro g v
        apply E.injective
        simp only [f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
          hE,MonoidHom.id_apply,coreToNatural_equivariant]
      · intro hz
        have hh := congrArg E hz
        have hp := NaturalGeometry.pairVector_ne_zero (by decide : (4 : Fin 6) ≠ 5)
        apply hp
        have hpair : coreToNatural (Fin 6) (pairWord 4 5)=NaturalGeometry.pairVector 4 5 := rfl
        simpa only [hpair,f,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
          map_zero] using hh
    · refine ⟨E.symm.toLinearMap,E.symm.surjective,?_,?_⟩
      · intro g v
        apply E.injective
        simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,hE,MonoidHom.id_apply]
      · intro hz
        have hh := congrArg E hz
        have hp : pairWord 4 5 ≠ 0 := by decide +kernel
        apply hp
        simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,map_zero] using hh
  obtain ⟨f,hf,hfe,hfn⟩ := hex
  obtain ⟨w,hw,htw⟩ := marked_cube u t ht hs
  let c := (MulAut.conj w).toMonoidHom
  let P₀ := P.comap c
  have hmap : P₀.map c=P := map_comap_eq_self_of_surjective (MulAut.conj w).surjective P
  have hP₀ : P₀ ≤ D 6 := by
    apply (map_le_map_iff_of_injective (f := c) (MulAut.conj w).injective).mp
    rw [hmap,hw]
    exact hP
  let τ := σ.comp c
  let f₀ := (σ w).comp f
  have hs₀ : Function.Surjective f₀ := by
    intro v
    obtain ⟨a,ha⟩ := hf (σ w⁻¹ v)
    refine ⟨a,?_⟩
    change σ w (f a)=v
    rw [ha,σ.self_inv_apply]
  have he₀ (g : S) (v : C) : f₀ (ρ g v)=τ g (f₀ v) := by
    change σ w (f (ρ g v))=σ (w*g*w⁻¹) (σ w (f v))
    rw [hfe]
    simp only [map_mul,Module.End.mul_apply,σ.inv_self_apply]
  have hn₀ : f₀ (pairWord 4 5) ≠ 0 := by
    intro hz
    have hh := congrArg (σ w⁻¹) hz
    apply hfn
    simpa only [f₀,LinearMap.comp_apply,σ.inv_self_apply,map_zero] using hh
  have hA : (zpowers swap45).map c=zpowers t := by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers htw
  have hT : (⊤ : Subgroup S).map c=⊤ := map_top_of_surjective c (MulAut.conj w).surjective
  have hh := mapped_canonical_dichotomy τ f₀ hs₀ he₀ hn₀ P₀ hP₀
  simpa only [τ,subspaceCommutator_comp_map,fixedSpace_comp_map,hA,hmap,hT] using hh
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentModel
