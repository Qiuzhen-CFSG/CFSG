module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedPairOrbit
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.MarkedPairOrbit

/-!
# A paired conjugator preserving the original mixed-edge marking

The mixed-plane orbit certificate and one explicit pair rotation supply
both source generation identities with a conjugator normalizing the original
three-pair cube. This retains the fixed plane used in MS93 (5.12)(3).
The private import is intentional coupling within the finite source-choice
proof; no internal definition occurs in the exported theorem.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
local notation "S" => Equiv.Perm (Fin 6)

private theorem top_of_star_mem (H : Subgroup S)
    (hs : ∀ i : Fin 5, Equiv.swap i.castSucc (5 : Fin 6) ∈ H) : H = ⊤ := by
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i,rfl⟩
  have cert : ∀ i : Fin 4, Equiv.swap (i.castSucc.castSucc : Fin 6) i.castSucc.succ =
      Equiv.swap i.castSucc.castSucc 5 * Equiv.swap i.succ.castSucc 5 *
        Equiv.swap i.castSucc.castSucc 5 := by decide +kernel
  fin_cases i
  · change Equiv.swap (0 : Fin 6) 1 ∈ H
    rw [show Equiv.swap (0 : Fin 6) 1 = _ from cert 0]
    exact H.mul_mem (H.mul_mem (hs 0) (hs 1)) (hs 0)
  · change Equiv.swap (1 : Fin 6) 2 ∈ H
    rw [show Equiv.swap (1 : Fin 6) 2 = _ from cert 1]
    exact H.mul_mem (H.mul_mem (hs 1) (hs 2)) (hs 1)
  · change Equiv.swap (2 : Fin 6) 3 ∈ H
    rw [show Equiv.swap (2 : Fin 6) 3 = _ from cert 2]
    exact H.mul_mem (H.mul_mem (hs 2) (hs 3)) (hs 2)
  · change Equiv.swap (3 : Fin 6) 4 ∈ H
    rw [show Equiv.swap (3 : Fin 6) 4 = _ from cert 3]
    exact H.mul_mem (H.mul_mem (hs 3) (hs 4)) (hs 3)
  · exact hs 4

private theorem canonical_choice :
    let A := plus.map (MulAut.conj cross).toMonoidHom
    A ⊔ A.map (MulAut.conj rotate).toMonoidHom = ⊤ ∧
      A ⊔ zpowers swap45 ⊔ zpowers ((MulAut.conj rotate⁻¹) swap45) = ⊤ ∧
      rotate ∈ normalizer ((D 6) : Set S) := by
  let A := plus.map (MulAut.conj cross).toMonoidHom
  have h1 : (MulAut.conj cross) (planeWords 0 1) ∈ A :=
    mem_map_of_mem _ ((mem_plus_iff _).mpr ⟨1,rfl⟩)
  have h2 : (MulAut.conj cross) (planeWords 0 2) ∈ A :=
    mem_map_of_mem _ ((mem_plus_iff _).mpr ⟨2,rfl⟩)
  refine ⟨?_,?_,?_⟩
  · let H := A ⊔ A.map (MulAut.conj rotate).toMonoidHom
    let gs : Fin 4 → S := ![(MulAut.conj cross) (planeWords 0 1),
      (MulAut.conj cross) (planeWords 0 2),
      (MulAut.conj rotate) ((MulAut.conj cross) (planeWords 0 1)),
      (MulAut.conj rotate) ((MulAut.conj cross) (planeWords 0 2))]
    have hgs (i : Fin 4) : gs i ∈ H := by
      fin_cases i
      · exact mem_sup_left h1
      · exact mem_sup_left h2
      · exact mem_sup_right (mem_map_of_mem _ h1)
      · exact mem_sup_right (mem_map_of_mem _ h2)
    let words : Fin 5 → List (Fin 4) :=
      ![[2,1,2], [3], [0,2,1,2,0], [1], [0,3,0]]
    have cert : ∀ i : Fin 5, ((words i).map gs).prod = Equiv.swap i.castSucc (5 : Fin 6) := by decide +kernel
    apply top_of_star_mem H
    intro i
    rw [←cert i]
    apply list_prod_mem
    intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact hgs j
  · let H := A ⊔ zpowers swap45 ⊔ zpowers ((MulAut.conj rotate⁻¹) swap45)
    let gs : Fin 4 → S := ![(MulAut.conj cross) (planeWords 0 1),
      (MulAut.conj cross) (planeWords 0 2),swap45,(MulAut.conj rotate⁻¹) swap45]
    have hgs (i : Fin 4) : gs i ∈ H := by
      fin_cases i
      · exact mem_sup_left (mem_sup_left h1)
      · exact mem_sup_left (mem_sup_left h2)
      · exact mem_sup_left (mem_sup_right (mem_zpowers _))
      · exact mem_sup_right (mem_zpowers _)
    let words : Fin 5 → List (Fin 4) :=
      ![[0,1,3,0,1], [0,2,0], [1,3,1], [1], [2]]
    have cert : ∀ i : Fin 5, ((words i).map gs).prod = Equiv.swap i.castSucc (5 : Fin 6) := by decide +kernel
    apply top_of_star_mem H
    intro i
    rw [←cert i]
    apply list_prod_mem
    intro x hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact hgs j
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff 3 x).mp hx
      have cert : ∀ i : Fin 8, ∃ j : Fin 8, (MulAut.conj rotate) (dWords i) = dWords j := by decide +kernel
      obtain ⟨j,hj⟩ := cert i
      exact (mem_disjointTranspositions_iff 3 _).mpr ⟨j,hj.symm⟩
    · rw [card_map_of_injective (MulAut.conj rotate).injective]

private theorem map_conj_map (A : Subgroup S) (r k : S) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj r).toMonoidHom =
      (A.map (MulAut.conj r).toMonoidHom).map
        (MulAut.conj ((MulAut.conj r) k)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change r*(k*x*k⁻¹)*r⁻¹=(r*k*r⁻¹)*(r*x*r⁻¹)*(r*k*r⁻¹)⁻¹
  group

private theorem choice_transport (A C : Subgroup S) (a k r : S)
    (h : A ⊔ A.map (MulAut.conj k).toMonoidHom = ⊤ ∧
      A ⊔ zpowers a ⊔ zpowers ((MulAut.conj k⁻¹) a) = ⊤ ∧
      k ∈ normalizer (C : Set S)) :
    let B := A.map (MulAut.conj r).toMonoidHom
    let b := (MulAut.conj r) a
    let l := (MulAut.conj r) k
    B ⊔ B.map (MulAut.conj l).toMonoidHom = ⊤ ∧
      B ⊔ zpowers b ⊔ zpowers ((MulAut.conj l⁻¹) b) = ⊤ ∧
      l ∈ normalizer (C.map (MulAut.conj r).toMonoidHom : Set S) := by
  refine ⟨?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj r).toMonoidHom) h.1
    rwa [Subgroup.map_sup,map_conj_map,map_top_of_surjective _ (MulAut.conj r).surjective] at hh
  · have hh := congrArg (Subgroup.map (MulAut.conj r).toMonoidHom) h.2.1
    rw [Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,
      map_top_of_surjective _ (MulAut.conj r).surjective] at hh
    have he : (MulAut.conj r) ((MulAut.conj k⁻¹) a) =
        (MulAut.conj ((MulAut.conj r) k)⁻¹) ((MulAut.conj r) a) := by
      change r*(k⁻¹*a*(k⁻¹)⁻¹)*r⁻¹=(r*k*r⁻¹)⁻¹*(r*a*r⁻¹)*((r*k*r⁻¹)⁻¹)⁻¹
      group
    change A.map (MulAut.conj r).toMonoidHom ⊔ zpowers ((MulAut.conj r) a) ⊔
      zpowers ((MulAut.conj r) ((MulAut.conj k⁻¹) a)) = ⊤ at hh
    rwa [he] at hh
  · rw [←map_normalizer_eq_of_bijective _ (MulAut.conj r).bijective]
    exact mem_map_of_mem _ h.2.2

private theorem marked_pair_base (u : S)
    (hgen : plus ⊔ plus.map (MulAut.conj u).toMonoidHom = ⊤) :
    ∃ k : S,
      plus.map (MulAut.conj u).toMonoidHom ⊔
        (plus.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k).toMonoidHom = ⊤ ∧
      plus.map (MulAut.conj u).toMonoidHom ⊔ zpowers swap45 ⊔
        zpowers ((MulAut.conj k⁻¹) swap45) = ⊤ ∧
      k ∈ normalizer ((D 6) : Set S) := by
  obtain ⟨r,hr,he⟩ := canonical_plane_orbit u hgen
  have hh := choice_transport (plus.map (MulAut.conj cross).toMonoidHom) (D 6)
    swap45 rotate r canonical_choice
  have hD : (D 6).map (MulAut.conj r).toMonoidHom = D 6 :=
    mem_normalizer_iff_map_conj_eq.mp (normalWords_mem_normalizer r hr)
  have ha : (MulAut.conj r) swap45 = swap45 := by
    have hc := normalWords_centralize r hr 2
    change r*swap45=swap45*r at hc
    change r*swap45*r⁻¹=swap45
    rw [hc,mul_inv_cancel_right]
  dsimp only at hh
  rw [←he,hD,ha] at hh
  exact ⟨(MulAut.conj r) rotate,hh⟩

/-- The paired source choice retains the original edge's cube normalizer.
Both generation identities use this same conjugator. -/
theorem mixed_marked_pair (u v a : S) (ha : a.IsSwap)
    (hmem : a ∈ plus.map (MulAut.conj v).toMonoidHom)
    (hgen : plus.map (MulAut.conj u).toMonoidHom ⊔
      plus.map (MulAut.conj v).toMonoidHom = ⊤) :
    ∃ k : S,
      plus.map (MulAut.conj u).toMonoidHom ⊔
        (plus.map (MulAut.conj u).toMonoidHom).map (MulAut.conj k).toMonoidHom = ⊤ ∧
      plus.map (MulAut.conj u).toMonoidHom ⊔ zpowers a ⊔
        zpowers ((MulAut.conj k⁻¹) a) = ⊤ ∧
      k ∈ normalizer (((D 6).map (MulAut.conj v).toMonoidHom) : Set S) := by
  have haeq : a = (MulAut.conj v) swap45 := by
    obtain ⟨b,hb,rfl⟩ := hmem
    obtain ⟨i,rfl⟩ := (mem_plus_iff b).mp hb
    have hc := Equiv.Perm.isSwap_iff_cycleType.mp ha
    change (v * planeWords 0 i * v⁻¹).cycleType = {2} at hc
    rw [Equiv.Perm.cycleType_conj] at hc
    have cert : ∀ i : Fin 4, (planeWords 0 i).cycleType = {2} → planeWords 0 i = swap45 := by decide +kernel
    rw [cert i hc]
    rfl
  have hmap : (plus.map (MulAut.conj (v⁻¹*u)).toMonoidHom).map (MulAut.conj v).toMonoidHom =
      plus.map (MulAut.conj u).toMonoidHom := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change v*((v⁻¹*u)*x*(v⁻¹*u)⁻¹)*v⁻¹=u*x*u⁻¹
    group
  have hbase : plus ⊔ plus.map (MulAut.conj (v⁻¹*u)).toMonoidHom = ⊤ := by
    apply map_injective (f := (MulAut.conj v).toMonoidHom) (MulAut.conj v).injective
    rw [Subgroup.map_sup,hmap,map_top_of_surjective _ (MulAut.conj v).surjective,sup_comm]
    exact hgen
  obtain ⟨k,hk⟩ := marked_pair_base (v⁻¹*u) hbase
  have hh := choice_transport (plus.map (MulAut.conj (v⁻¹*u)).toMonoidHom) (D 6)
    swap45 k v hk
  dsimp only at hh
  rw [hmap,←haeq] at hh
  exact ⟨(MulAut.conj v) k,hh⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
