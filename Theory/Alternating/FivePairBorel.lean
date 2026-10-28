module
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal

/-!
# Sylow control in a two-factor A₅ Borel

A {2,3}-subgroup of A₅ containing a Sylow two-subgroup is proper, hence lies
in that Sylow normalizer. Apply this to both literal projections of an
A₅ × A₅ subgroup. The original Sylow subgroup is the product of its two
projections, so the whole subgroup normalizes it.

Source application: Aschbacher–Smith, 10.2.3, printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.Alternating.FiveSylowMaximal
namespace Theory.AlternatingFive
local notation "A" => alternatingGroup (Fin 5)

private theorem six_subgroup_ne_top (P : Subgroup A) (hP : IsPGroup 6 P) : P ≠ ⊤ := by
  intro he
  have hA : IsPGroup 6 A := (he ▸ hP).of_equiv Subgroup.topEquiv
  obtain ⟨n,hn⟩ := hA.exists_card_dvd_pow
  have hfive : 5 ∣ Nat.card A := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hh := Nat.prime_five.dvd_of_dvd_pow (hfive.trans hn)
  norm_num at hh

/-- A {2,3}-overgroup of the actual Sylow subgroup lies in its Borel. -/
theorem pair_six_overgroup_le_sylow_normalizer
    (S : Sylow 2 (A × A)) (P : Subgroup (A × A))
    (hP : IsPGroup 6 P) (hSP : (S : Subgroup (A × A)) ≤ P) :
    P ≤ normalizer (S : Set (A × A)) := by
  let S1 := S.mapSurjective (f := MonoidHom.fst A A) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := MonoidHom.snd A A) (fun x => ⟨(1,x),rfl⟩)
  have htwo : IsPGroup 2 ((S1 : Subgroup A).prod (S2 : Subgroup A)) := by
    obtain ⟨a,ha⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := S2.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := a+b) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add])
  have hle : (S : Subgroup (A × A)) ≤ (S1 : Subgroup A).prod (S2 : Subgroup A) := by
    intro x hx
    exact ⟨mem_map_of_mem (MonoidHom.fst A A) hx,mem_map_of_mem (MonoidHom.snd A A) hx⟩
  have he : (S : Subgroup (A × A)) = (S1 : Subgroup A).prod (S2 : Subgroup A) :=
    (S.is_maximal' htwo hle).symm
  have h1 := overgroup_le_sylow_normalizer S1 (P.map (MonoidHom.fst A A))
    (map_mono hSP) (six_subgroup_ne_top _ (hP.map _))
  have h2 := overgroup_le_sylow_normalizer S2 (P.map (MonoidHom.snd A A))
    (map_mono hSP) (six_subgroup_ne_top _ (hP.map _))
  intro x hx
  have hx1 := h1 (mem_map_of_mem (MonoidHom.fst A A) hx)
  have hx2 := h2 (mem_map_of_mem (MonoidHom.snd A A) hx)
  rw [show (S : Set (A × A)) = ((S1 : Subgroup A).prod (S2 : Subgroup A) : Set (A × A))
    from congrArg SetLike.coe he]
  apply mem_normalizer_iff.mpr
  rintro ⟨a,b⟩
  exact (mem_normalizer_iff.mp hx1 a).and (mem_normalizer_iff.mp hx2 b)

end Theory.AlternatingFive
