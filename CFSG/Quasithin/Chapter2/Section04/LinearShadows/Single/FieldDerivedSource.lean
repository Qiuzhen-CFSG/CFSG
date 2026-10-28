module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InsideFieldFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFixedCardSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import Theory.GroupTheory.ElementaryFixedQuotientLifting
public import Theory.GroupTheory.FixedIntersectionDerived

/-!
# The fixed center lies in the derived group of the inside centralizer

A nontrivial fixed root quotient has a fixed lift through Q, because its
elementary-kernel cocycle is a coboundary. Commutation with this lift maps
C_Q(s) onto C_Z(R)(s): its kernel is C_Z(R)(s), and the actual field-action
orders give |C_Q(s)|=|C_Z(R)(s)|². Thus the fixed center lies in C_R(s)′.
The R-conjugacy of every involution of S outside R to a marked field
involution transports this inclusion to the literal source involution.

Source: Aschbacher–Smith, Lemma 2.4.12(2) and the centerless inside branch
of Lemma 2.4.21(2), printed pp.532 and 536.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_centerless_field_fixed_center_le_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hcenter : center (d.block.map d.H.subtype) = ⊥)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    let I := R ⊓ centralizer ({s} : Set G)
    Z ⊓ centralizer ({s} : Set G) ≤ ⁅I,I⁆ := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Q := twoCore d.H
  let N := Q.subgroupOf R
  let : N.Normal := source_field_core_normal d
  let Z := R ⊓ centralizer (R : Set G)
  let I := R ⊓ centralizer ({s} : Set G)
  have hgeom := source_thompson_root_geometry d hG T hST hsingle hL hM hTM hunique
  change Q ≤ R ∧ Z ≤ Q ∧ ⁅R,R⁆ ≤ Z ∧
    ∀ r ∈ R, r ∉ Q → Q ⊓ centralizer ({r} : Set G) = Z at hgeom
  have hsR : s ∉ R := by
    intro hr
    have he : (⟨s,hs.1⟩:S)=1 := disjoint_def.mp c.split_sylow.disjoint hr hs
    have hs1 : s=1 := congrArg Subtype.val he
    simp [hs1] at hs2
  have han : s ∉ centralizer (Z : Set G) := by
    intro hc
    have he := source_centerless_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique c hcenter
    rw [distinguishedZ_of_centerless d hcenter] at he
    change S⊓centralizer (Z:Set G)=R at he
    exact hsR (he ▸ (show s∈S⊓centralizer (Z : Set G) from ⟨hs.1,hc⟩))
  have hs1 : s^2=1 := by simpa only [hs2] using pow_orderOf_eq_one s
  obtain ⟨m,hm,hn,hZfix⟩ := source_centerless_center_involution_fixed_card d hG T hST hsingle hL
    hM hTM hunique c hcenter s (hST.le hs.1) hs1 han
  have hQfix : Nat.card (Q ⊓ centralizer ({s} : Set G) : Subgroup G)=2^n := by
    have hc := source_centerless_field_plane_card d hG T hST hsingle hL hM hTM hunique c hcenter s hs hs2
    rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2] at hc
    exact hc
  let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
  let hN : ∀ x ∈ N, α x ∈ N := source_field_actor_preserves_core d s hs.1
  let : IsElementaryAbelian 2 N :=
    (source_field_elementary_layers d hG T hST hsingle hL hM hTM hunique c).1
  have hα : Function.Involutive α := by
    intro r
    apply Subtype.ext
    change s*(s*(r:G)*s⁻¹)*s⁻¹=(r:G)
    calc
      _ = (s*s)*(r:G)*(s*s)⁻¹ := by group
      _ = (r:G) := by rw [show s*s=1 from by simpa only [pow_two] using hs1]; simp
  have hcN := source_field_involution_core_fixed_card d hG T hST hsingle hL hM hTM hunique c s hs hs2
  have hcQ := source_field_involution_sylow_quotient_fixed_card d hG T hST hsingle hL hM hTM hunique c s hs hs2
  change Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N))^2=Nat.card N at hcN
  change Nat.card ((QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N)))^2=Nat.card (R ⧸ N) at hcQ
  have hcroot : 1 < Nat.card ((QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))) := by
    rw [source_centerless_root_quotient_card d hG T hST hsingle hL hM hTM hunique c hcenter] at hcQ
    have hp : 1<2^n := Nat.one_lt_pow (by have := hL.1; omega) (by decide)
    nlinarith
  obtain ⟨r,hrfix,hrN⟩ := Theory.GroupTheory.exists_fixed_outside_of_elementary_kernel N α hα hN hcN hcroot
  have hrI : (r:G) ∈ I := ⟨r.property,mem_centralizer_singleton_iff.mpr (by
    have he := congrArg Subtype.val hrfix
    change s*(r:G)*s⁻¹=(r:G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm)⟩
  have hQI : Q ⊓ I = Q ⊓ centralizer ({s} : Set G) := by
    rw [show I=R⊓centralizer ({s}:Set G) from rfl,←inf_assoc,inf_eq_left.mpr hgeom.1]
  have hZI : Z ⊓ I = Z ⊓ centralizer ({s} : Set G) := by
    rw [show I=R⊓centralizer ({s}:Set G) from rfl,←inf_assoc,inf_eq_left.mpr inf_le_left]
  have hcount : Nat.card (Q⊓I : Subgroup G)=Nat.card (Z⊓I : Subgroup G)^2 := by
    rw [hQI,hZI,hQfix,hZfix,hn,←pow_mul]
    congr 1
    omega
  have hd := Theory.GroupTheory.fixed_intersection_le_commutator_of_card_sq Q Z I (r:G) hrI
    ((show Z≤centralizer (R:Set G) from inf_le_right).trans (centralizer_le hgeom.1))
    (hgeom.2.2.2 r r.property hrN)
    (fun q hq => hgeom.2.2.1 (commutator_mem_commutator (hgeom.1 hq) r.property)) hcount
  change Z⊓centralizer ({s}:Set G)≤⁅I,I⁆
  rwa [hZI] at hd

theorem source_centerless_inside_fixed_center_le_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (hcenter : center (d.block.map d.H.subtype) = ⊥)
    (a : G) (haS : a ∈ (d.S : Subgroup d.H).map d.H.subtype) (ha2 : orderOf a = 2)
    (haR : a ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    let I := R ⊓ centralizer ({a} : Set G)
    Z ⊓ centralizer ({a} : Set G) ≤ ⁅I,I⁆ := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Z := R ⊓ centralizer (R : Set G)
  obtain ⟨s,hs,hs2,r,hr,he⟩ := source_inside_involution_conj_field d hG T hST hsingle hL hM hTM hunique c a haS ha2 haR
  have hd := source_centerless_field_fixed_center_le_derived d hG T hST hsingle hL hM hTM hunique c hcenter s hs hs2
  change Z⊓centralizer ({s}:Set G)≤⁅R⊓centralizer ({s}:Set G),R⊓centralizer ({s}:Set G)⁆ at hd
  let e := MulAut.conj r
  have hRmap : R.map e.toMonoidHom=R := mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hr)
  have hrZ : r∈normalizer (Z:Set G) :=
    inf_normalizer_le_normalizer_inf ⟨R.le_normalizer hr,
      normalizer_le_normalizer_centralizer R (R.le_normalizer hr)⟩
  have hZmap : Z.map e.toMonoidHom=Z := mem_normalizer_iff_map_conj_eq.mp hrZ
  have hCmap : (centralizer ({s}:Set G)).map e.toMonoidHom=centralizer ({a}:Set G) := by
    rw [Theory.GroupTheory.map_centralizer_equiv,Set.image_singleton]
    change centralizer ({r*s*r⁻¹}:Set G)=_
    rw [he]
  have hm := map_mono (f:=e.toMonoidHom) hd
  rw [map_inf _ _ _ e.injective,hZmap,hCmap,map_commutator,
    map_inf _ _ _ e.injective,hRmap,hCmap] at hm
  exact hm


end CFSG.Quasithin.Chapter2.LinearShadows.Single
