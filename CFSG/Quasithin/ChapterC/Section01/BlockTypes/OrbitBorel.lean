module
public import Theory.GroupTheory.CommutingCoreBorels
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation
public import CFSG.Quasithin.Chapter1.Section01
/-!
# The Borel orbit of a quasisimple short block

For a short subnormal K with quasisimple two-core quotient, distinct
Sylow conjugates commute by C.1.9. Their Sylow normalizers have
characteristic two and normal Sylow two-subgroups. The commuting-family
calculation therefore gives both properties for the actual orbit
⟨N_K(S∩K)^S⟩, including its odd quotient by its two-core.

Source: Aschbacher--Smith 15.1.20, third paragraph, printed p.1094.
Only the local group containing K and its Sylow is used here; invariance
under an external marked overgroup is a separate statement.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

private theorem borel_eq (S K : Subgroup G) :
    K ⊓ normalizer ((S ⊓ K : Subgroup G) : Set G) =
      (normalizer (S.subgroupOf K : Set K)).map K.subtype := by
  have he : S.subgroupOf K = (S ⊓ K).subgroupOf K := by
    ext x
    exact ⟨fun h => ⟨h,x.property⟩,fun h => h.1⟩
  rw [he,←subgroupOf_normalizer_eq (show S ⊓ K ≤ K from inf_le_right),subgroupOf_map_subtype]
  exact inf_comm _ _

private theorem borel_conj (S K : Subgroup G) (g : G)
    (hg : g ∈ normalizer (S : Set G)) :
    (K ⊓ normalizer ((S ⊓ K : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom =
      K.map (MulAut.conj g).toMonoidHom ⊓
        normalizer ((S ⊓ K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_equiv_normalizer_eq,
    map_inf _ _ _ (MulAut.conj g).injective]
  have he : S.map (MulAut.conj g).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp hg
  rw [he]

private theorem normalizer_core (P : Sylow 2 G) :
    ∃ R : Sylow 2 (normalizer (P : Set G)),
      (R : Subgroup (normalizer (P : Set G))) = pCore 2 (normalizer (P : Set G)) := by
  let N := normalizer (P : Set G)
  let R := P.subtype P.le_normalizer
  have hn : ((P : Subgroup G).subgroupOf N).Normal :=
    normal_subgroupOf_of_le_normalizer (by exact le_rfl)
  refine ⟨R,le_antisymm ?_ (pCore_isPGroup.le_sylow_of_normal R)⟩
  exact le_sSup ⟨hn,R.isPGroup'⟩

variable [Finite G]

/-- The literal orbit of the Sylow Borel in a quasisimple short block has
characteristic two and a normal Sylow two-subgroup. -/
theorem IsBlock.orbit_borel_structure (S : Sylow 2 G) {K : Subgroup G}
    (hK : IsBlock K) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    let B := conjugateSpanBy (K ⊓ normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) (S : Subgroup G)
    generalizedFitting B = pCore 2 B ∧
      (∃ P : Sylow 2 B, (P : Subgroup B) = pCore 2 B) ∧
      Odd (Nat.card (B ⧸ pCore 2 B)) := by
  classical
  let I := {X : Subgroup G // X ∈ Set.range fun s : S => K.map (MulAut.conj (s : G)).toMonoidHom}
  let C : I → Subgroup G := fun i => i.val ⊓ normalizer (((S : Subgroup G) ⊓ i.val : Subgroup G) : Set G)
  have hblock (i : I) : IsBlock i.val := by
    obtain ⟨s,he⟩ := i.property
    rw [←he]
    exact hK.map_equiv (MulAut.conj (s : G))
  have hquasi (i : I) : IsQuasisimple (i.val ⧸ pCore 2 i.val) := by
    obtain ⟨s,he⟩ := i.property
    rw [←he]
    let e := (MulAut.conj (s : G)).subgroupMap K
    let := hq
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hc : Pairwise fun i j => C i ≤ centralizer (C j : Set G) := by
    intro i j hij
    have hne : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hh := (hblock i).commutator_eq_bot_of_quasisimple_quotient
      (hblock j) (hquasi i) hne
    exact inf_le_left.trans ((commutator_eq_bot_iff_le_centralizer.mp hh).trans
      (centralizer_le inf_le_left))
  have hC (i : I) :
      C i ⊓ centralizer ((C i).pCoreIn 2 : Set G) ≤ (C i).pCoreIn 2 ∧
      ∃ P : Sylow 2 (C i), (P : Subgroup (C i)) = pCore 2 (C i) := by
    obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal i.val (hblock i).subnormal
    let N := normalizer (P : Set i.val)
    have heN : N.map i.val.subtype = C i := by
      change (normalizer ((P : Subgroup i.val) : Set i.val)).map i.val.subtype = _
      rw [hP]
      exact (borel_eq (S : Subgroup G) i.val).symm
    let e : N ≃* C i := (equivMapOfInjective N i.val.subtype i.val.subtype_injective).trans
      (MulEquiv.subgroupCongr heN)
    have hnself := centralizer_pCore_le_of_sylow_le P N P.le_normalizer
      ((hblock i).short.fitting ▸ centralizer_generalizedFitting_le i.val)
    have hself := (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hnself
    refine ⟨Chapter1.mem_He_iff.mpr hself,?_⟩
    obtain ⟨R,hR⟩ := normalizer_core P
    refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
    change (R : Subgroup N).map e.toMonoidHom = _
    rw [hR,pCore_map_iso]
  have hgen : (⨆ i, C i) =
      conjugateSpanBy (K ⊓ normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)) (S : Subgroup G) := by
    rw [conjugateSpanBy_eq_iSup_conj]
    apply le_antisymm
    · apply iSup_le
      intro i
      obtain ⟨s,he⟩ := i.property
      dsimp only at he
      have hh := borel_conj (S : Subgroup G) K s ((S : Subgroup G).le_normalizer s.property)
      have heC : C i = (K ⊓ normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)).map
          (MulAut.conj (s : G)).toMonoidHom := by
        rw [hh,he]
      rw [heC]
      exact le_iSup (fun t : S => (K ⊓ normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G)).map
        (MulAut.conj (t : G)).toMonoidHom) s
    · apply iSup_le
      intro s
      rw [borel_conj _ _ _ ((S : Subgroup G).le_normalizer s.property)]
      exact le_iSup C ⟨_,⟨s,rfl⟩⟩
  rw [←hgen]
  have hself := Chapter1.mem_He_iff.mp
    (core_centralizer_iSup_of_commuting C hc (fun i => (hC i).1))
  obtain ⟨P,hP⟩ := exists_sylow_eq_core_of_commuting C hc (fun i => (hC i).2)
  refine ⟨generalizedFitting_eq_pCore_of_selfCentralizing 2 hself,⟨P,hP⟩,?_⟩
  apply Nat.not_even_iff_odd.mp
  intro hh
  have hd : 2 ∣ (pCore 2 (⨆ i, C i : Subgroup G)).index := even_iff_two_dvd.mp hh
  rw [←hP] at hd
  exact P.not_dvd_index hd
end CFSG.Quasithin.ChapterC
