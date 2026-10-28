module

public import Stellmacher.Recognition.Parrott.SylowCoreSelectionData
public import Theory.GroupTheory.CentralBinaryCentralizerCard
public import Theory.GroupTheory.CyclicExtension

/-!
# Four dual rows generate Parrott's original core

The supplied three-generator data and a fourth element c with the prescribed
commutators give the antidiagonal pairing against t,v,u,w. No completed frame
or generation assumption is used. In the elementary derived subgroup E,
commuting with a,b,c,d successively eliminates w,u,v,t, leaving only ⟨z⟩.

Put L = ⟨a,b,c,d⟩. The restricted central binary pairing between E and LE,
together with C_G(E) = E, gives |LE| = 512. Thus LE is the actual ambient
two-core J. Transporting this equality to the native core and using
E = Φ(J), Frattini nongeneration gives L = J. All coordinates are retained.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.673–674 and p.679, equations (9)–(10).
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

private theorem remove_coordinate [Finite G] (A : Subgroup G)
    [IsElementaryAbelian 2 A] (S : Set G) (g r : G)
    (hS : S ⊆ A) (hg : g ∈ A) (hrg : ¬ Commute r g)
    (hrS : ∀ s ∈ S, Commute r s) {k : G}
    (hk : k ∈ closure (insert g S)) (hrk : Commute r k) : k ∈ closure S := by
  obtain ⟨y, hy, i, hi⟩ := Theory.GroupTheory.exists_mul_pow_of_mem_closure_insert
    S g 2 (by decide) (elemPow_eq_one_of_isElementaryAbelian g hg)
    (fun s hs => by
      rw [(setLike_mul_comm hg (hS hs) : g*s=s*g), mul_inv_cancel_right]
      exact subset_closure hs) hk
  have hrc : closure S ≤ centralizer ({r} : Set G) := by
    apply (closure_le _).mpr
    intro s hs
    exact mem_centralizer_singleton_iff.mpr (hrS s hs).symm.eq
  have hry : Commute r y := (mem_centralizer_singleton_iff.mp (hrc hy)).symm
  fin_cases i
  · have he : y = k := by simpa using hi
    exact he ▸ hy
  · have he : k = y*g := by simpa using hi.symm
    rw [he] at hrk ⊢
    exfalso
    apply hrg
    change r*g=g*r
    apply mul_left_cancel (a := y)
    calc
      y*(r*g) = r*(y*g) := by rw [← mul_assoc, ← hry.eq, mul_assoc]
      _ = (y*g)*r := hrk.eq
      _ = y*(g*r) := mul_assoc _ _ _

private theorem three_commute_d_v (f : ParrottSylowThreeGeneratorData n) :
    Commute f.d n.v := by
  have hd : f.d⁻¹ = f.d := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using f.d_sq)
  have hv : n.v⁻¹ = n.v := inv_eq_of_mul_eq_one_right
    (by have hv : n.v ^ 2 = 1 := n.v_order ▸ pow_orderOf_eq_one n.v
        simpa only [pow_two] using hv)
  have heq : f.d * n.v = f.b⁻¹ * f.d * f.b := by
    rw [← f.eq03_db]
    simp only [Tits.parrottCommutator]
    group
  have heq' := congrArg Inv.inv heq
  simp only [mul_inv_rev, hd, hv, inv_inv] at heq'
  exact heq.trans (by simpa only [mul_assoc] using heq'.symm)

/-- The four supplied rows are dual, in reverse order, to t,v,u,w. -/
public theorem ParrottSylowThreeGeneratorData.fourth_pairing_entries
    (f : ParrottSylowThreeGeneratorData n) (c : G)
    (hcu : Tits.parrottCommutator c f.u = 1)
    (hcw : Tits.parrottCommutator c f.w = 1)
    (hct : Tits.parrottCommutator c n.t = 1)
    (hcv : Tits.parrottCommutator c n.v = z) (i j : Fin 4) :
    Tits.parrottCommutator (![f.a,f.b,c,f.d] i) (![n.t,n.v,f.u,f.w] j) =
      z ^ (if i.val + j.val = 3 then 1 else 0) := by
  let : IsElementaryAbelian 2 e.F := e.elementary
  have hF (g : G) (hg : g ∈ ({z,n.t,n.v,f.u,f.a} : Set G)) : g ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure hg
  have hat : Tits.parrottCommutator f.a n.t = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr
      (setLike_mul_comm (hF _ (by simp)) (hF _ (by simp)))
  have hav : Tits.parrottCommutator f.a n.v = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr
      (setLike_mul_comm (hF _ (by simp)) (hF _ (by simp)))
  have hau : Tits.parrottCommutator f.a f.u = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr
      (setLike_mul_comm (hF _ (by simp)) (hF _ (by simp)))
  have hbt := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.comm_bt
  have hbv := (Tits.parrottCommutator_eq_one_iff _ _).mpr
    (show Commute f.b n.v by rw [← f.eq03_b]; exact Commute.self_pow _ _)
  have hdv := (Tits.parrottCommutator_eq_one_iff _ _).mpr (three_commute_d_v f)
  fin_cases i <;> fin_cases j <;>
    simp [hat, hav, hau, hbt, hbv, hdv, f.eq02_aw, f.eq02_bu, f.eq02_bw,
      hct, hcv, hcu, hcw, f.eq03_dt, f.eq08_du, f.eq07_dw]

/-- Four prescribed dual commutator rows generate the original two-core. -/
public theorem ParrottSylowThreeGeneratorData.fourth_generates [Finite G]
    (f : ParrottSylowThreeGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (c : G) (hc : c ∈ J)
    (hcu : Tits.parrottCommutator c f.u = 1)
    (hcw : Tits.parrottCommutator c f.w = 1)
    (hct : Tits.parrottCommutator c n.t = 1)
    (hcv : Tits.parrottCommutator c n.v = z) :
    closure ({f.a, f.b, c, f.d} : Set G) = J := by
  let K := pCore 2 H
  let D := commutator K
  let embed := (H).subtype.comp K.subtype
  have hinj : Function.Injective embed := (H).subtype_injective.comp K.subtype_injective
  obtain ⟨hZ, _, _, hPhi, hUpper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map embed
  have hEF (g : G) (hg : g ∈ ({z,n.t,n.v,f.u,f.a} : Set G)) : g ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure hg
  have hEE (g : G) (hg : g ∈ ({z,n.t,n.v,f.u,f.w} : Set G)) : g ∈ E := by
    rw [← f.derived_basis]
    exact subset_closure hg
  have ha : f.a ∈ J := e.le_core (hEF _ (by simp))
  have hEJ : E ≤ J := by
    rintro g ⟨k, _, rfl⟩
    exact mem_map_of_mem (H).subtype k.property
  have hzcomm {g : G} (hg : g ∈ J) : Commute g z :=
    mem_centralizer_singleton_iff.mp (map_subtype_le _ hg)
  have haz := hzcomm ha
  have hbz := hzcomm f.b_mem_core
  have hcz := hzcomm hc
  have hdz := hzcomm f.d_mem_core
  have rows := f.fourth_pairing_entries c hcu hcw hct hcv
  have hat : Commute f.a n.t := (Tits.parrottCommutator_eq_one_iff _ _).mp
    (by simpa using rows 0 0)
  have hav : Commute f.a n.v := (Tits.parrottCommutator_eq_one_iff _ _).mp
    (by simpa using rows 0 1)
  have hau : Commute f.a f.u := (Tits.parrottCommutator_eq_one_iff _ _).mp
    (by simpa using rows 0 2)
  have hbv : Commute f.b n.v := (Tits.parrottCommutator_eq_one_iff _ _).mp
    (by simpa using rows 1 1)
  have hct' : Commute c n.t := (Tits.parrottCommutator_eq_one_iff _ _).mp
    (by simpa using rows 2 0)
  have hne : z ≠ 1 := by intro hz; have := h.involution; simp [hz] at this
  have noncomm {r s : G} (hrs : Tits.parrottCommutator r s = z) : ¬ Commute r s := by
    intro hh
    exact hne (hrs.symm.trans ((Tits.parrottCommutator_eq_one_iff _ _).mpr hh))
  let L := closure ({f.a,f.b,c,f.d} : Set G)
  have hLJ : L ≤ J := by
    apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    exact ha
    exact f.b_mem_core
    exact hc
    exact f.d_mem_core
  have hfixed : E ⊓ centralizer (L : Set G) ≤ zpowers z := by
    intro k hk
    have hkcomm (r : G) (hr : r ∈ ({f.a,f.b,c,f.d} : Set G)) : Commute r k :=
      hk.2 r (subset_closure hr)
    have hkE : k ∈ closure ({f.w,f.u,n.v,n.t,z} : Set G) := by
      have hset : ({f.w,f.u,n.v,n.t,z} : Set G) = {z,n.t,n.v,f.u,f.w} := by
        ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset, f.derived_basis]
      exact hk.1
    have hw := remove_coordinate E ({f.u,n.v,n.t,z} : Set G) f.w f.a
      (by intro s hs; apply hEE; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢; tauto)
      (hEE _ (by simp)) (noncomm f.eq02_aw)
      (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl | rfl | rfl <;> assumption) hkE (hkcomm _ (by simp))
    have hu := remove_coordinate E ({n.v,n.t,z} : Set G) f.u f.b
      (by intro s hs; apply hEE; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢; tauto)
      (hEE _ (by simp)) (noncomm f.eq02_bu)
      (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl | rfl; exact hbv; exact f.comm_bt; exact hbz)
      hw (hkcomm _ (by simp))
    have hv := remove_coordinate E ({n.t,z} : Set G) n.v c
      (by intro s hs; apply hEE; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢; tauto)
      (hEE _ (by simp)) (noncomm hcv)
      (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
          rcases hs with rfl | rfl <;> assumption) hu (hkcomm _ (by simp))
    have ht := remove_coordinate E ({z} : Set G) n.t f.d
      (by intro s hs; obtain rfl := Set.mem_singleton_iff.mp hs; exact hEE _ (by simp))
      (hEE _ (by simp)) (noncomm f.eq03_dt)
      (by intro s hs; obtain rfl := Set.mem_singleton_iff.mp hs; exact hdz)
      hv (hkcomm _ (by simp))
    simpa only [← zpowers_eq_closure] using ht
  let B := L ⊔ E
  have hBJ : B ≤ J := sup_le hLJ hEJ
  have hEB : E ≤ B := le_sup_right
  have hZcentral : zpowers z ≤ centralizer (B : Set G) := by
    rintro q ⟨i, rfl⟩ b hb
    exact ((hzcomm (hBJ hb)).zpow_right i).eq
  have hfixedB : E ⊓ centralizer (B : Set G) = zpowers z := by
    apply le_antisymm
    · exact (inf_le_inf_left _ (centralizer_le (show (L : Set G) ⊆ B from fun _ hx => (le_sup_left : L ≤ B) hx))).trans hfixed
    · exact le_inf (zpowers_le.mpr (hEE _ (by simp))) hZcentral
  have hcomm : ⁅E, B⁆ ≤ zpowers z := by
    apply commutator_le.mpr
    rintro a ⟨aK, haK, rfl⟩ b hb
    obtain ⟨bH, hbK, rfl⟩ := hBJ hb
    have hab : ⁅aK, (⟨bH,hbK⟩ : K)⁆ ∈ center K := by
      have haU := hUpper ▸ haK
      simpa only [Subgroup.upperCentralSeries_one] using
        (Subgroup.mem_upperCentralSeries_succ_iff.mp haU (⟨bH,hbK⟩ : K))
    rw [← hZ]
    exact mem_map_of_mem embed hab
  have hZcomm : ⁅zpowers z, B⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_eq_bot_iff_le_centralizer]
    exact hZcentral
  have hcardE : Nat.card E = 32 := (card_map_of_injective hinj).trans hDcard
  have hcount := card_mul_card_centralizer_restrict_of_central_binary_pairing
    E B (zpowers z) (zpowers_le.mpr (hEE _ (by simp))) hcomm hZcomm
    ((Nat.card_zpowers z).trans h.involution)
  have hright : Nat.card ((centralizer (E : Set G)).subgroupOf B) = 32 := by
    rw [parrott_derived_centralizer z h]
    exact (Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv).trans hcardE
  have hleft : Nat.card ((centralizer (B : Set G)).subgroupOf E) = 2 := by
    rw [← card_map_of_injective (E).subtype_injective, subgroupOf_map_subtype,
      inf_comm, hfixedB, Nat.card_zpowers, h.involution]
  rw [hcardE, hright, hleft] at hcount
  have hBJ_eq : B = J := eq_of_le_of_card_ge hBJ (by
    rw [card_map_of_injective (H).subtype_injective, h.core_card]
    omega)
  have hrange : embed.range = J := by
    rw [MonoidHom.range_comp, range_subtype]
  have hmap : (L.comap embed).map embed = L := map_comap_eq_self (hrange.symm ▸ hLJ)
  have htop : L.comap embed ⊔ frattini K = ⊤ := by
    apply map_injective hinj
    rw [Subgroup.map_sup, hmap, ← hPhi, ← MonoidHom.range_eq_map, hrange]
    exact hBJ_eq
  have hLtop := frattini_nongenerating htop
  change L = J
  rw [← hmap, hLtop, ← MonoidHom.range_eq_map, hrange]
end Stellmacher.Recognition
