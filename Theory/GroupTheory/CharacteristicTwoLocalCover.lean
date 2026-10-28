module

public import Theory.GroupTheory.FourGroupNormalizerOvergroup
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.PGroup.ElementaryNormalizer

/-!
# Characteristic-two local covers and transport

A two-local containing a Sylow two-subgroup is the normalizer of a nontrivial
subgroup normal in that Sylow subgroup. Thus a finite normal-subgroup
calculation can cover all such two-locals. The characteristic-center
reduction further restricts that calculation to elementary subgroups. A cover by characteristic-two
subgroups gives equality for a subgroup maximal subject to F*=O₂.

The second step is transported through actual group isomorphisms, preserving
the intrinsic generalized Fitting subgroup and prime cores. It requires
neither maximality among all two-locals nor ambient normality of the local
subgroup. The application is the model inspection in Aschbacher--Smith,
15.3.41--42, printed p.1138; the covering family remains an explicit input.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {H : Type*} [Group H]

/-- Every two-local containing a Sylow two-subgroup is the normalizer of
a nontrivial subgroup normal in that Sylow subgroup. -/
theorem exists_normal_sylow_witness [Finite H] (P : Sylow 2 H) (N : Subgroup H)
    (hlocal : IsTwoLocal N) (hPN : (P : Subgroup H) ≤ N) :
    ∃ U : Subgroup H, U ≠ ⊥ ∧ U ≤ (P : Subgroup H) ∧
      (U.subgroupOf (P : Subgroup H)).Normal ∧ N = normalizer (U : Set H) := by
  obtain ⟨U, hU, hpU, rfl⟩ := hlocal
  let PN := P.subtype hPN
  let hn : (U.subgroupOf (normalizer (U : Set H))).Normal := inferInstance
  have hUP : U ≤ (P : Subgroup H) := by
    intro x hx
    exact (show IsPGroup 2 (U.subgroupOf (normalizer (U : Set H))) from
      hpU.comap_subtype).le_sylow_of_normal PN
      (show (⟨x, U.le_normalizer hx⟩ : normalizer (U : Set H)) ∈
        U.subgroupOf (normalizer (U : Set H)) from hx)
  exact ⟨U, hU, hUP, (normal_subgroupOf_iff_le_normalizer hUP).mpr hPN, rfl⟩

/-- Replacing a two-local witness by its characteristic elementary center
gives a normal elementary subgroup of the same Sylow group and a containing
normalizer. No maximality or ambient characteristic-two assumption is needed. -/
theorem exists_normal_elementary_sylow_overgroup [Finite H] (P : Sylow 2 H) (N : Subgroup H)
    (hlocal : IsTwoLocal N) (hPN : (P : Subgroup H) ≤ N) :
    ∃ E : Subgroup H, E ≠ ⊥ ∧ E ≤ (P : Subgroup H) ∧
      (E.subgroupOf (P : Subgroup H)).Normal ∧ IsElementaryAbelian 2 E ∧
      N ≤ normalizer (E : Set H) := by
  obtain ⟨U, hU, hUP, _, hN⟩ := exists_normal_sylow_witness P N hlocal hPN
  have hpU : IsPGroup 2 U :=
    P.isPGroup'.of_injective (inclusion hUP) (inclusion_injective hUP)
  obtain ⟨E, hE, hEU, hEle, hUE⟩ :=
    U.exists_nontrivial_elementary_with_normalizer_le hpU hU
  have hNE : N ≤ normalizer (E : Set H) := hN ▸ hUE
  have hEP : E ≤ (P : Subgroup H) := hEU.trans hUP
  exact ⟨E, hE, hEP, (normal_subgroupOf_iff_le_normalizer hEP).mpr (hPN.trans hNE),
    hEle, hNE⟩


/-- Transport maximality subject to the intrinsic condition F*=O₂. -/
theorem maximal_characteristicTwo_map {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) (N : Subgroup A)
    (hmax : ∀ J : Subgroup A, N ≤ J →
      generalizedFitting J = pCore 2 J → J = N) :
    ∀ J : Subgroup B, N.map f.toMonoidHom ≤ J →
      generalizedFitting J = pCore 2 J → J = N.map f.toMonoidHom := by
  intro J hNJ hJ
  have hpre : N ≤ J.map f.symm.toMonoidHom := by
    simpa [Subgroup.map_map] using Subgroup.map_mono (f := f.symm.toMonoidHom) hNJ
  have he : J.map f.symm.toMonoidHom = N :=
    hmax _ hpre (characteristicTwo_of_mulEquiv (f.symm.subgroupMap J).symm hJ)
  have hm := congrArg (Subgroup.map f.toMonoidHom) he
  simpa [Subgroup.map_map] using hm

/-- An actual group equivalence identifies the intrinsic two-core quotients. -/
noncomputable def coreQuotientEquiv {A B : Type*} [Group A] [Group B] (f : A ≃* B) :
    (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
  QuotientGroup.congr _ _ f (pCore_map_iso 2 f)

/-- The order of the three-core of the two-core quotient is invariant under isomorphism. -/
theorem threeCore_quotient_card_eq {A B : Type*} [Group A] [Group B] (f : A ≃* B) :
    Nat.card (pCore 3 (A ⧸ pCore 2 A)) = Nat.card (pCore 3 (B ⧸ pCore 2 B)) := by
  let q := coreQuotientEquiv f
  rw [← pCore_map_iso 3 q]
  exact (card_map_of_injective (f := q.toMonoidHom) q.injective).symm

/-- A conjugate covering family of characteristic-two groups gives actual
local isomorphisms when the original subgroup is maximal subject to F*=O₂. -/
theorem local_equiv_of_cover {A B ι : Type*} [Group A] [Group B] [Finite A]
    (f : A ≃* B) (C : ι → Subgroup B) (P : Sylow 2 A) (N : Subgroup A)
    (hlocal : IsTwoLocal N) (hPN : (P : Subgroup A) ≤ N)
    (hF : generalizedFitting N = pCore 2 N)
    (hmax : ∀ J : Subgroup A, N ≤ J → generalizedFitting J = pCore 2 J → J = N)
    (hcharacteristic : ∀ i : ι, generalizedFitting (C i) = pCore 2 (C i))
    (hcover : ∀ (T : Sylow 2 B) (D : Subgroup B),
      IsTwoLocal D → (T : Subgroup B) ≤ D → generalizedFitting D = pCore 2 D →
      ∃ (i : ι) (g : B), D ≤ (C i).map (MulAut.conj g).toMonoidHom) :
    ∃ i : ι, Nonempty (N ≃* C i) := by
  let T := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hT : (T : Subgroup B) ≤ N.map f.toMonoidHom := map_mono hPN
  have hD : generalizedFitting (N.map f.toMonoidHom) = pCore 2 (N.map f.toMonoidHom) :=
    characteristicTwo_of_mulEquiv (f.subgroupMap N).symm hF
  obtain ⟨i, g, hle⟩ := hcover T (N.map f.toMonoidHom)
    (Theory.Quasithin.isTwoLocal_map f hlocal) hT hD
  have hg : N.map f.toMonoidHom = (C i).map (MulAut.conj g).toMonoidHom :=
    (maximal_characteristicTwo_map f N hmax _ hle
      (characteristicTwo_of_mulEquiv ((MulAut.conj g).subgroupMap (C i)).symm
        (hcharacteristic i))).symm
  exact ⟨i, ⟨(f.subgroupMap N).trans
    ((MulEquiv.subgroupCongr hg).trans ((MulAut.conj g).subgroupMap _).symm)⟩⟩

end Theory.GroupTheory
