module
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.Hall.OddNormalProducts
/-!
# The omega-center centralizer in a minimal outside overgroup

A proper centralizer of the Sylow omega-center contains the prescribed
Sylow subgroup, hence lies in the maximal-local overlap by H-star
minimality. An odd Hall subgroup complements that Sylow subgroup in the
overlap. If its pointwise action on the omega-center is faithful, the
centralizer is exactly the Sylow subgroup. This is the literal seed
centralizer needed by the natural-source selection in 10.2.3(4).

Source: Aschbacher–Smith 3.1.2–3 and 10.2.3(4), pp.571–572 and745–746.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M H : Subgroup G}

/-- Faithful odd Hall action removes the odd part of the seed centralizer. -/
theorem HStar.omega_center_centralizer_eq_sylow_of_hall
    (hH : H ∈ HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (B : Subgroup H) (_hBM : B ≤ M.subgroupOf H)
    (hHall : IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (B.subgroupOf (M.subgroupOf H)))
    (hfaith : B.map H.subtype ⊓
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥) :
    centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype hH.1.1.2 : Subgroup H) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm
  have hCH : H ⊓ centralizer (Z : Set G) < H := lt_of_le_of_ne inf_le_left (by
    intro he
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    rw [←he]
    exact inf_le_right)
  have hCM : H ⊓ centralizer (Z : Set G) ≤ M :=
    HStar.proper_overgroup_le T hH (le_inf hH.1.1.2 hTZ) hCH
  have hTM : (T : Subgroup G) ≤ M :=
    (le_inf hH.1.1.2 hTZ).trans hCM
  let TH := T.subtype hH.1.1.2
  let S := TH.subtype (show (TH : Subgroup H) ≤ M.subgroupOf H from fun _ hx => hTM hx)
  have hprod := (OddHall.sylow_complement_of_hall S hHall).symm
  apply le_antisymm
  · intro x hx
    have hxZ : (x:G) ∈ centralizer (Z : Set G) := by
      intro z hz
      exact congrArg H.subtype (hx ⟨z,hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1⟩ hz)
    let y : M.subgroupOf H := ⟨x,hCM ⟨x.property,hxZ⟩⟩
    obtain ⟨b,hb,t,ht,he⟩ := Set.mem_mul.mp (hprod.mul_eq.symm ▸ Set.mem_univ y)
    have htT : ((t:H):G) ∈ (T : Subgroup G) := ht
    have hbZ : ((b:H):G) ∈ centralizer (Z : Set G) := by
      have heG : ((b:H):G) * ((t:H):G) = (x:G) :=
        congrArg (fun a : M.subgroupOf H => ((a:H):G)) he
      have hbG : ((b:H):G) = (x:G) * (((t:H):G))⁻¹ := by
        exact eq_mul_inv_iff_mul_eq.mpr heG
      rw [hbG]
      exact (centralizer (Z : Set G)).mul_mem hxZ
        ((centralizer (Z : Set G)).inv_mem (hTZ htT))
    have hb1 : ((b:H):G)=1 := by
      have hh : ((b:H):G) ∈ B.map H.subtype ⊓
          centralizer (Z : Set G) := ⟨mem_map_of_mem H.subtype hb,hbZ⟩
      simpa only [Z,hfaith,mem_bot] using hh
    have heG : ((b:H):G) * ((t:H):G) = (x:G) :=
        congrArg (fun a : M.subgroupOf H => ((a:H):G)) he
    change (x:G) ∈ (T : Subgroup G)
    rw [←heG,hb1,one_mul]
    exact htT
  · intro t ht z hz
    apply Subtype.ext
    exact hTZ ht z hz
end CFSG.Quasithin.Chapter3
