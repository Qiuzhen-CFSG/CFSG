module
public import Theory.GroupTheory.PResidual.CoreCentralizer
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.Noncentrality

/-!
# The larger action kernel in the original centralizer

Put H=C_G(z), U=⟨Ω₁(Z(T))^H⟩, K=C_H(U), and D=O²(K), with every
subgroup embedded by its literal inclusion. The earlier 13.4.4(ii) says
that the original R₁ is Sylow in C_H(D/O₂(D)). The residual-section
calculation then proves C_R₁(U)=O₂(H). Normality of that section
centralizer gives T-normalization of R₁, contains I=⟨J(R₁)^H⟩, and
makes R₁ Sylow in IR₁. No equality K=O₂(H) is used.

The first theorem identifies this construction with C_H(L₊/O₂(L₊))
when the earlier source identifies D with L₊. The final theorem applies
the local data to the existing Baumann noncentrality argument and the
actual Thompson quotient: I* is S₃ or S₃×S₃, and J(R₁)* is its Sylow
subgroup. This removes the kernel-intersection and normalization premises
from that application in the larger-kernel, Baumann-bound branch.

Earlier 13.4.4(ii) retains final discharge with qt-d-1341-fixed-core-source.
The short-block noncentrality argument for this kernel, selection of the
single factor, the original R₁ identification, IT uniqueness, the C₃ chamber
and ambient involution-fusion assembly remain with qt-d-1341-solvable-source.
This module does not establish full 13.4.8–9.

Source: Aschbacher–Smith 13.4.4(2), printed p.897, and 13.4.8,
printed pp.904–905.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original larger-kernel section centralizer, embedded in G. -/
def centralizerResidualSection (T : Sylow 2 G) (z : G) : Subgroup G :=
  let H := centralizer ({z} : Set G)
  let K := centralizer ((centralizerOmegaOrbit T z).subgroupOf H : Set H)
  (residualSectionCentralizer 2 K).map H.subtype

/-- The section is literally C_H(A/O₂(A)) when earlier 13.4.4 identifies
A with O²(C_H(V_H)); this retains the original ambient embedding. -/
theorem centralizerResidualSection_eq_of_residual
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (A : Subgroup G)
    (hA : let H := centralizer ({z} : Set G)
      let K := centralizer ((centralizerOmegaOrbit T z).subgroupOf H : Set H)
      ((pResidual 2 K).map K.subtype).map H.subtype = A) :
    centralizerResidualSection T z =
      commutatorPreimage (centralizer ({z} : Set G)) A (A.pCoreIn 2) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let K := centralizer (U : Set H)
  let D := (pResidual 2 K).map K.subtype
  let : D.Normal := inferInstance
  let : (D.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 D).map D.subtype).Normal
  let C := residualSectionCentralizer 2 K
  have hD : D.map H.subtype = A := hA
  have hcore : (D.pCoreIn 2).map H.subtype = A.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 D H.subtype H.subtype_injective,hD]
  have hncore : H ≤ normalizer (A.pCoreIn 2 : Set G) := by
    rw [← hcore]
    have hh := (D.pCoreIn 2).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  change C.map H.subtype = commutatorPreimage H A (A.pCoreIn 2)
  apply le_antisymm
  · apply le_commutatorPreimage (map_subtype_le _)
    have hh := map_mono (f := H.subtype)
      (commutator_commutatorPreimage_le ⊤ D (D.pCoreIn 2) le_normalizer_of_normal)
    rwa [map_commutator,hD,hcore] at hh
  · let B := commutatorPreimage H A (A.pCoreIn 2)
    have hBH : B ≤ H := commutatorPreimage_le _ _ _
    have hBC : B.subgroupOf H ≤ C := by
      apply le_commutatorPreimage le_top
      apply (map_le_map_iff_of_injective H.subtype_injective).mp
      rw [map_commutator,map_subgroupOf_eq_of_le hBH,hD,hcore]
      exact commutator_commutatorPreimage_le H A (A.pCoreIn 2) hncore
    have hh := map_mono (f := H.subtype) hBC
    rwa [map_subgroupOf_eq_of_le hBH] at hh

omit [Finite G] in
private theorem sylow_in_intermediate {p : ℕ} {A B : Subgroup G}
    (S : Sylow p A) (hBA : B ≤ A) (hSB : (S : Subgroup A).map A.subtype ≤ B) :
    ∃ P : Sylow p B, (P : Subgroup B).map B.subtype = (S : Subgroup A).map A.subtype := by
  let f := inclusion hBA
  have hSr : (S : Subgroup A) ≤ f.range := by
    intro s hs
    exact ⟨⟨s,hSB (mem_map_of_mem A.subtype hs)⟩,rfl⟩
  refine ⟨S.comapOfInjective f (inclusion_injective hBA) hSr, ?_⟩
  apply le_antisymm
  · rintro x ⟨b,hb,rfl⟩
    exact ⟨f b,hb,rfl⟩
  · rintro x ⟨a,ha,rfl⟩
    exact ⟨⟨a,hSB (mem_map_of_mem A.subtype ha)⟩,ha,rfl⟩

/-- Case (ii) gives the exact kernel intersection and the original Sylow placement. -/
theorem centralizer_larger_kernel_local_data
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))).subtype).map
          (centralizer ({z} : Set G)).subtype = R) :
    R ⊓ centralizer (centralizerOmegaOrbit T z : Set G) =
        (centralizer ({z} : Set G)).pCoreIn 2 ∧
      (T : Subgroup G) ≤ normalizer (R : Set G) ∧
      conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G)) ≤
        centralizerResidualSection T z ∧
      ∃ P : Sylow 2 (conjugateSpanBy (elementaryAbelianMaxJ R)
          (centralizer ({z} : Set G)) ⊔ R : Subgroup G),
        (P : Subgroup _).map
          (conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G)) ⊔ R).subtype = R := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let K := centralizer (U : Set H)
  let C := residualSectionCentralizer 2 K
  let := residualSectionCentralizer_normal (p := 2) K
  let Ri := (S : Subgroup C).map C.subtype
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hRH : R ≤ H := hRT.trans hTH
  have hRi : Ri = R.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hRH]
    exact hR
  have hQK : pCore 2 H ≤ K := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hcore : Ri ⊓ K = pCore 2 H :=
    sylow_residualSectionCentralizer_inf_eq_pCore K hQK S
  have hQR : H.pCoreIn 2 ≤ R := by
    have hh := map_mono (f := H.subtype) (hcore.symm.le.trans inf_le_left)
    rwa [hR] at hh
  have hc : R ⊓ centralizer (centralizerOmegaOrbit T z : Set G) = H.pCoreIn 2 := by
    apply le_antisymm
    · intro x hx
      have hxR : (⟨x,hRH hx.1⟩ : H) ∈ Ri := hRi.symm ▸ hx.1
      have hxK : (⟨x,hRH hx.1⟩ : H) ∈ K := by
        intro u hu
        exact Subtype.ext (hx.2 u.val hu)
      exact mem_map_of_mem H.subtype (hcore ▸ (show (⟨x,hRH hx.1⟩ : H) ∈ Ri ⊓ K from ⟨hxR,hxK⟩))
    · refine le_inf hQR ?_
      rintro x ⟨a,ha,rfl⟩ u hu
      exact congrArg Subtype.val ((hQK ha) ⟨u,centralizerOmegaOrbit_le hz hu⟩ hu)
  have hCn : H ≤ normalizer (C.map H.subtype : Set G) := by
    have hh := C.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hRC : R ≤ C.map H.subtype := by
    rw [← hR]
    exact map_mono (map_subtype_le _)
  have hRiT : Ri ≤ (T.subtype hTH : Sylow 2 H) := by
    rw [hRi]
    exact fun x hx => hRT hx
  have hi := inf_eq_sylow_map S (T.subtype hTH).isPGroup' hRiT
  have hRinf : (T : Subgroup G) ⊓ C.map H.subtype = R := by
    have hm := congrArg (map H.subtype) hi
    rw [map_inf _ _ _ H.subtype_injective,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTH,hR] at hm
    exact hm
  have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [← hRinf]
    exact (le_inf (T : Subgroup G).le_normalizer (hTH.trans hCn)).trans
      inf_normalizer_le_normalizer_inf
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  have hIC : I ≤ C.map H.subtype := conjugateSpanBy_le
    ((sSup_le fun _ hA => hA.1).trans hRC) hCn
  refine ⟨hc,hnR,hIC,?_⟩
  let e := C.equivMapOfInjective H.subtype H.subtype_injective
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hs' : (S' : Subgroup (C.map H.subtype)).map (C.map H.subtype).subtype = R := by
    change ((S : Subgroup C).map e.toMonoidHom).map (C.map H.subtype).subtype = R
    rw [map_map]
    change (S : Subgroup C).map (H.subtype.comp C.subtype) = R
    rw [← map_map]
    exact hR
  obtain ⟨P,hP⟩ := sylow_in_intermediate S' (sup_le hIC hRC)
    (by rw [hs']; exact le_sup_right)
  exact ⟨P,hP.trans hs'⟩


/-- With the earlier Baumann bound, case (ii) supplies the actual noncentral
Thompson action, its one-or-two-factor model and its marked Sylow image. -/
theorem centralizer_thompson_models_of_larger_kernel
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))).subtype).map
          (centralizer ({z} : Set G)).subtype = R)
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G))) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let I := ((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q
    ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G) ∧
      (Nonempty (I ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty (I ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) ∧
      ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype =
        ((elementaryAbelianMaxJ R).subgroupOf H).map q := by
  obtain ⟨hc,hnR,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz hz1 R hRT S hR
  have hQR := hc.symm.le.trans inf_le_left
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hc hB hout
  exact ⟨hJ,centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv,
    centralizer_thompson_span_sylow h₀ hz hz1 R hRT hnR hQR hJ hsolv⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
