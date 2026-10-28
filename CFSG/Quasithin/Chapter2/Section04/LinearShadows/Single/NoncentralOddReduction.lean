module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OddClassClosureSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OddComplementSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldSylowOrbitSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionFusionSource
/-!
# The odd noncentral contradiction from the inside class subgroup

The actual outside fixed center controls the entire Δ-involution class in
a Sylow subgroup of the outside involution centralizer. A nonabelian
class-generated subgroup in the inside centralizer therefore prevents fusion
of the two actors. Original field-coset fusion and Thompson transfer finish
the odd half-degree contradiction.

Source: Aschbacher–Smith, Lemma 2.4.24(2), printed p.540. The final theorem
isolates precisely the inside nonabelian class subgroup supplied by the
marked orthogonal fixed-group construction; it assumes no Sylow recognition
or full fixed-model classification.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
include hG hST hsingle hL hM hTM hunique

theorem source_noncenterless_outside_not_field_of_nonabelian_delta_class
    (c : CyclicTorusSetup d T n)
    (hclosed : ∀ r t:T, orderOf r=2 →
      (r:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype) →
      IsConj (r:G) (t:G) → (t:G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (x : G) (hxT : x∈T) (hxS : x∉(d.S:Subgroup d.H).map d.H.subtype)
    (hxB : x∈normalizer (c.hall:Set G)) (hx2 : x^2=1)
    (s u : G) (hu : u∈distinguishedDelta d x)
    (hI : ¬IsMulCommutative (closure {v:G |
      v∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓centralizer ({s}:Set G) ∧ IsConj u v})) :
    ¬IsConj s x := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let A := R⊓centralizer (R:Set G)
  let V := A⊓centralizer ({x}:Set G)
  let C := centralizer ({x}:Set G)
  let I := R⊓centralizer ({s}:Set G)
  have hRT : R≤(T:Subgroup G) := (show R≤S from sSup_le fun _ h=>h.1).trans hST.le
  have hVR : V≤R := inf_le_left.trans inf_le_left
  have hVp : IsPGroup 2 V := T.isPGroup'.to_le (hVR.trans hRT)
  have hVC : V≤C := inf_le_right
  let : IsMulCommutative V := le_centralizer_iff_isMulCommutative.mp
    ((show V≤centralizer (R:Set G) from inf_le_left.trans inf_le_right).trans (centralizer_le hVR))
  obtain ⟨P,hVP⟩ := (hVp.comap_subtype (K:=C)).exists_le_sylow
  have hVP' : V≤(P:Subgroup C).map C.subtype := by
    intro v hv
    exact ⟨⟨v,hVC hv⟩,hVP hv,rfl⟩
  apply not_isConj_of_nonabelian_class_and_abelian_sylow_class u s x I
    (T.isPGroup'.to_le (inf_le_left.trans hRT)) inf_le_right hI P V
  exact source_noncenterless_outside_elementary_class_closure d hG T hST hsingle hL hM hTM hunique
    c hclosed hz x hxT hxS hxB hx2 u hu ((P:Subgroup C).map C.subtype)
    (P.isPGroup'.map C.subtype) (map_subtype_le _) hVP'

theorem source_noncentral_odd_false_of_nonabelian_delta_class
    (c : CyclicTorusSetup d T n) (s : T)
    (hs : (s:G)∈(d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G)∉Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) (hn : Odd (n/2))
    (hinside : ∀ x∈T, x∉(d.S:Subgroup d.H).map d.H.subtype →
      x∈normalizer (c.hall:Set G) → ∀ u∈distinguishedDelta d x,
      ¬IsMulCommutative (closure {v:G |
        v∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓
          centralizer ({(s:G)}:Set G) ∧ IsConj u v})) : False := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let A := R⊓centralizer (R:Set G)
  have hclosed := CyclicTorusSetup.involution_fusion_closed d hG T hST hsingle hL hM hTM hunique c
  have hRS : R≤S := sSup_le fun _ h=>h.1
  have hRT : R≤(T:Subgroup G) := hRS.trans hST.le
  obtain ⟨x,hxT,hxS,hxB,hxord⟩ := source_odd_half_degree_outside_involution d hG T hST hsingle hL hM hTM hunique c s hs hs2 hclosed hn
  have hx2 : x^2=1 := by simpa only [hxord] using pow_orderOf_eq_one x
  let V := A⊓centralizer ({x}:Set G)
  have hV : V≠⊥ := by
    have hc := (source_noncenterless_outside_center_fixed_data d hG T hST hsingle hL hM hTM hunique hz x hxT hxS hx2).1
    intro he
    change Nat.card V=2^n at hc
    rw [he,card_bot] at hc
    have hn' := hL.1
    have hh : 1<2^n := Nat.one_lt_pow (by omega) (by decide)
    omega
  obtain ⟨u,hu,hu1⟩ := V.bot_or_exists_ne_one.resolve_left hV
  have huDelta := source_noncenterless_outside_fixed_nonidentity_mem_delta d hG T hST hsingle hL hM hTM hunique hz x hxT hxS u hu hu1
  have hsx := source_noncenterless_outside_not_field_of_nonabelian_delta_class d hG T hST hsingle hL hM hTM hunique c hclosed hz x hxT hxS hxB hx2 (s:G) u huDelta (hinside x hxT hxS hxB u huDelta)
  have hindex := (d.lemma_2_4_8_1 hG T hST hsingle
    (hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective))).1
  let C := S.subgroupOf (T:Subgroup G)
  let : C.Normal := C.normal_of_index_eq_two hindex
  let : IsCyclic (T⧸C) := isCyclic_of_prime_card (p:=2) hindex
  obtain ⟨t,hxt,htS⟩ := cyclic_quotient_forces_involution_fusion hG T C
    ⟨x,hxT⟩ ((orderOf_coe (⟨x,hxT⟩:T)).symm.trans hxord)
  have htord : orderOf t=2 := by
    rw [←orderOf_coe]
    exact (SemiconjBy.orderOf_eq (hxt.choose:G) hxt.choose_spec).symm.trans hxord
  have htR : (t:G)∉R := by
    intro htR
    exact hxS (hRS (hclosed t ⟨x,hxT⟩ htord htR hxt.symm))
  obtain ⟨r,hr,he⟩ := source_field_involution_sylow_fusion d hG T hST hsingle hL hM hTM hunique c (s:G) hs ((orderOf_coe s).trans hs2) hsR (t:G) htS ((orderOf_coe t).trans htord) htR
  exact hsx ((isConj_iff.mpr ⟨r,he⟩).trans hxt.symm)
/-- A pair of noncommuting elements in the prescribed inside Δ-class
is the only marked fixed-group input needed by the transfer argument. -/
theorem source_noncentral_odd_false_of_noncommuting_delta_pair
    (c : CyclicTorusSetup d T n) (s : T)
    (hs : (s:G)∈(d.S:Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : (s:G)∉Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hz : center (d.block.map d.H.subtype) ≠ ⊥) (hn : Odd (n/2))
    (hpair : ∀ x∈T, x∉(d.S:Subgroup d.H).map d.H.subtype →
      x∈normalizer (c.hall:Set G) → ∀ u∈distinguishedDelta d x,
      ∃ r t:G,
        r∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓centralizer ({(s:G)}:Set G) ∧
        t∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓centralizer ({(s:G)}:Set G) ∧
        IsConj r u ∧ IsConj t u ∧ ¬Commute r t) : False := by
  apply source_noncentral_odd_false_of_nonabelian_delta_class d hG T hST hsingle hL hM hTM hunique c s hs hs2 hsR hz hn
  intro x hxT hxS hxB u hu
  obtain ⟨r,t,hrI,htI,hru,htu,hrt⟩ := hpair x hxT hxS hxB u hu
  intro hab
  let H := closure {v:G | v∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)⊓centralizer ({(s:G)}:Set G) ∧ IsConj u v}
  let : IsMulCommutative H := hab
  have hrH : r∈H := subset_closure ⟨hrI,hru.symm⟩
  have htH : t∈H := subset_closure ⟨htI,htu.symm⟩
  exact hrt (congrArg Subtype.val (mul_comm (⟨r,hrH⟩:H) ⟨t,htH⟩))
end CFSG.Quasithin.Chapter2.LinearShadows.Single
