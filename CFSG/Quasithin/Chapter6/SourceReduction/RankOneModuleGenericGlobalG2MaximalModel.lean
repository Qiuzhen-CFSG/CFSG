module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionG2ShortModel

/-!
# The short G₂ core above field order four

A subfield containing every cube is the whole field when its order exceeds
four: the cubic polarization gives x²+x, and any proper such subfield would
force x⁴=x for every field element. Apply this to the scalar stabilizer of
an additive root-coordinate subgroup. The short rank-one torus acts by
cubes on the isolated first coordinate, while root and Weyl conjugations
supply all four coordinates. Thus a subgroup of the five-root radical
normalized by the local factor lies in its center or equals the radical.

The adjacent maximality module applies this to the actual right residual
in the prepared pair. The field-four case is deliberately excluded: its
local action alone does not supply the full-parabolic irreducibility.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653, and F.1.12(I)(3),
pp.262–264 (`refs/quasithin.pdf`). The coordinate argument adapts
RankOneModuleGenericGlobalRecognitionG2ShortModel and uses the existing
licensed ATLAS root calculations; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional ATLAS source is copied here.
-/

public noncomputable section

open Subgroup
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Maximal
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem subfield_eq_top_of_cubes (hq : 4 < Nat.card F)
    (K : Subfield F) (hc : ∀ x : F, x^3 ∈ K) : K = ⊤ := by
  by_contra hn
  obtain ⟨b,hb⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hn)
  have hb' : b ∉ K := hb.2
  have hqmem (x : F) : x^2+x ∈ K := by
    have hh := K.sub_mem (K.sub_mem (hc (x+1)) (hc x)) K.one_mem
    convert hh using 1
    ring_nf
    all_goals simp [CharTwo.ofNat_eq_mod]
  have hid (a : F) (ha : a ∈ K) : a^2+a = 0 := by
    by_contra hne
    have hh : b*(a^2+a) ∈ K := by
      have hh := K.sub_mem (hqmem (b*a)) (K.mul_mem (K.pow_mem ha 2) (hqmem b))
      convert hh using 1
      simp only [CharTwo.sub_eq_add]
      ring_nf
      all_goals simp [CharTwo.ofNat_eq_mod]
    apply hb'
    have hh' := K.div_mem hh (hqmem a)
    simpa only [mul_div_cancel_right₀ _ hne] using hh'
  have hpow (x : F) : x^4 = x := by
    have hh := hid (x^2+x) (hqmem x)
    have he : (x^2+x)^2+(x^2+x) = x^4+x := by
      ring_nf
      simp [CharTwo.ofNat_eq_mod]
    rw [he] at hh
    simpa only [add_eq_zero_iff_eq_neg,CharTwo.neg_eq] using hh
  classical
  let := Fintype.ofFinite F
  open Polynomial in
  have hbound := card_le_degree_of_subset_roots (R := F) (p := X^4-X)
    (Z := Finset.univ) (fun x _ => by
      apply mem_roots'.mpr
      exact ⟨FiniteField.X_pow_card_sub_X_ne_zero F (by decide : 1 < 4), by
        simp only [IsRoot,eval_sub,eval_pow,eval_X,hpow,sub_self]⟩)
  simp only [Finset.card_univ,FiniteField.X_pow_card_sub_X_natDegree_eq F (by decide : 1 < 4),
    ← Nat.card_eq_fintype_card] at hbound
  omega

private theorem mul_mem_of_cubes (hq : 4 < Nat.card F)
    (W : AddSubgroup F) (hc : ∀ a b : F, b ∈ W → a^3*b ∈ W) :
    ∀ a b : F, b ∈ W → a*b ∈ W := by
  let K : Subring F := {
    carrier := {a | ∀ b ∈ W, a*b ∈ W}
    zero_mem' := by intro b hb; simp
    one_mem' := by intro b hb; simpa using hb
    add_mem' := by intro a c ha hc b hb; simpa [add_mul] using W.add_mem (ha b hb) (hc b hb)
    mul_mem' := by intro a c ha hc b hb; simpa [mul_assoc] using ha (c*b) (hc b hb)
    neg_mem' := by intro a ha b hb; simpa using W.neg_mem (ha b hb) }
  have hcube (a : F) : a^3 ∈ K := hc a
  have hinv (a : F) (ha : a ∈ K) : a⁻¹ ∈ K := by
    by_cases hz : a=0
    · simp [hz]
    have hh := K.mul_mem (hcube a⁻¹) (K.pow_mem ha 2)
    convert hh using 1
    field_simp
  let E : Subfield F := K.toSubfield hinv
  have he : E = ⊤ := subfield_eq_top_of_cubes hq E hcube
  intro a b hb
  exact (show a ∈ E from he.symm ▸ trivial) b hb

private theorem horizontal_dichotomy (hq : 4 < Nat.card F)
    (W : AddSubgroup (Fin 4 → F))
    (hs : ∀ a b c d e, ![b,c,d,e] ∈ W →
      ![b+a*c+a^2*d+a^3*e,c+a^2*e,d+a*e,e] ∈ W)
    (hw : ∀ b c d e, ![b,c,d,e] ∈ W → ![e,d,c,b] ∈ W)
    (hcube : ∀ a b : F, ![b,0,0,0] ∈ W → ![a^3*b,0,0,0] ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  let v : F →+ (Fin 4 → F) := {
    toFun b := ![b,0,0,0]
    map_zero' := by ext i; fin_cases i <;> rfl
    map_add' := by intro a b; ext i; fin_cases i <;> simp }
  have ht (a : Fˣ) (b : F) (hb : ![b,0,0,0] ∈ W) : ![(a:F)*b,0,0,0] ∈ W :=
    mul_mem_of_cubes hq (W.comap v) hcube a b hb
  classical
  let := Fintype.ofFinite F
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset F).card < (Finset.univ : Finset F).card by
      have htwo : 2 < Nat.card F := by omega
      simpa [Nat.card_eq_fintype_card] using htwo)
  have hkk : k ≠ 0 ∧ k ≠ 1 := by simpa using hk
  have hk0 := hkk.1
  have hk1 := hkk.2
  have hk2 : k + k^2 ≠ 0 := by
    rw [show k+k^2 = k*(1+k) by ring]
    apply mul_ne_zero hk0
    intro h
    have h1 := eq_neg_of_add_eq_zero_right h
    exact hk1 (by simpa only [CharTwo.neg_eq] using h1)
  have hd (a b c d e : F) (h : ![b,c,d,e] ∈ W) :
      ![a*c+a^2*d+a^3*e,a^2*e,a*e,0] ∈ W := by
    have hh := W.sub_mem (hs a b c d e h) h
    convert hh using 1
    ext i
    fin_cases i <;> simp
    all_goals ring
  by_cases hex : ∃ b : F, b ≠ 0 ∧ ![b,0,0,0] ∈ W
  · obtain ⟨b,hb,hbW⟩ := hex
    have hB (z : F) : ![z,0,0,0] ∈ W := by
      by_cases hz : z = 0
      · subst z
        convert W.zero_mem using 1
        ext i
        fin_cases i <;> rfl
      · simpa only [Units.val_mk0,div_mul_cancel₀ _ hb] using ht (Units.mk0 (z/b) (div_ne_zero hz hb)) b hbW
    have hE (z : F) : ![0,0,0,z] ∈ W := hw z 0 0 0 (hB z)
    have hCD (a z : F) : ![0,a^2*z,a*z,0] ∈ W := by
      have hh := W.sub_mem (hd a 0 0 0 z (hE z)) (hB (a^3*z))
      convert hh using 1
      ext i
      fin_cases i <;> simp
    have hC (z : F) : ![0,z,0,0] ∈ W := by
      let v := z/(k+k^2)
      have hh := W.add_mem (hCD k v) (hCD 1 (k*v))
      have he : k^2*v+k*v = z := by
        rw [←add_mul,add_comm (k^2) k]
        exact mul_div_cancel₀ z hk2
      convert hh using 1
      ext i
      fin_cases i <;>
        simp [he,CharTwo.add_self_eq_zero]
    have hD (z : F) : ![0,0,z,0] ∈ W := hw 0 z 0 0 (hC z)
    right
    apply top_unique
    intro v _
    convert W.add_mem (W.add_mem (hB (v 0)) (hC (v 1)))
      (W.add_mem (hD (v 2)) (hE (v 3))) using 1
    ext i
    fin_cases i <;> simp
  · have hB (b : F) (h : ![b,0,0,0] ∈ W) : b = 0 := by
      by_contra hb
      exact hex ⟨b,hb,h⟩
    left
    apply le_antisymm _ bot_le
    intro v hv
    have hh : ![v 0,v 1,v 2,v 3] ∈ W := by
      convert hv using 1
      ext i
      fin_cases i <;> rfl
    have htwice := hd k (v 1+v 2+v 3) (v 3) (v 3) 0
      (by simpa using hd 1 (v 0) (v 1) (v 2) (v 3) hh)
    have he : v 3 = 0 := by
      have he := hB (k*v 3+k^2*v 3) (by simpa using htwice)
      rw [←add_mul] at he
      exact (mul_eq_zero.mp he).resolve_left hk2
    have hcd : v 1 + v 2 = 0 :=
      hB _ (by simpa [he] using hd 1 (v 0) (v 1) (v 2) (v 3) hh)
    have hcd' : v 1 = v 2 := by simpa only [add_eq_zero_iff_eq_neg,CharTwo.neg_eq] using hcd
    have hdz : v 2 = 0 := by
      have hh := hB _ (by simpa [he,hcd'] using hd k (v 0) (v 1) (v 2) (v 3) hh)
      rw [←add_mul] at hh
      exact (mul_eq_zero.mp hh).resolve_left hk2
    have hcz : v 1 = 0 := hcd'.trans hdz
    have hbz : v 0 = 0 := hB _ (by simpa [he,hcz,hdz] using hh)
    change v = 0
    ext i
    fin_cases i <;> simp [hbz,hcz,hdz,he]


private def rad (t : Fin 6 → F) (ht : t 5 = 0) : radical₁ (F := F) :=
  ⟨unipotentProduct t, t, ht, rfl⟩

private def horizontal : radical₁ (F := F) →* Multiplicative (Fin 4 → F) where
  toFun r := Multiplicative.ofAdd ![unipotentParameters r.val 1,
    unipotentParameters r.val 2,unipotentParameters r.val 3,unipotentParameters r.val 4]
  map_one' := by
    apply Multiplicative.toAdd.injective
    have hh : (1 : Model F) = unipotentProduct 0 := by simp [unipotentProduct]
    change ![unipotentParameters 1 1,unipotentParameters 1 2,
      unipotentParameters 1 3,unipotentParameters 1 4] = 0
    rw [hh,unipotentParameters_product]
    ext i
    fin_cases i <;> rfl
  map_mul' r s := by
    obtain ⟨t,ht,he⟩ := r.property
    obtain ⟨u,hu,hf⟩ := s.property
    apply Multiplicative.toAdd.injective
    change ![unipotentParameters (r.val*s.val) 1,unipotentParameters (r.val*s.val) 2,
      unipotentParameters (r.val*s.val) 3,unipotentParameters (r.val*s.val) 4] = _
    rw [←he,←hf,unipotentProduct_mul,unipotentParameters_product]
    ext i
    fin_cases i <;> simp [unipotentProductParameters,unipotentParameters_product,ht,add_comm]

omit [Finite F] [CharP F 2] in
private theorem horizontal_rad (t : Fin 6 → F) (ht : t 5 = 0) :
    horizontal (rad t ht) = Multiplicative.ofAdd ![t 1,t 2,t 3,t 4] := by
  change Multiplicative.ofAdd _ = _
  rw [show (rad t ht).val = unipotentProduct t from rfl,unipotentParameters_product]

omit [Finite F] in
private theorem horizontal_ker : (horizontal (F := F)).ker = center (radical₁ (F := F)) := by
  ext r
  obtain ⟨t,ht,he⟩ := r.property
  have hr : r = rad t ht := Subtype.ext he.symm
  rw [hr,MonoidHom.mem_ker,horizontal_rad]
  constructor
  · intro hh
    have hz (i : Fin 4) := congrFun (congrArg Multiplicative.toAdd hh) i
    have h1 : t 1 = 0 := hz 0
    have h2 : t 2 = 0 := hz 1
    have h3 : t 3 = 0 := hz 2
    have h4 : t 4 = 0 := hz 3
    have hh : rad t ht = radicalCentral (t 0) := by
      apply Subtype.ext
      simp [rad,radicalCentral,unipotentProduct,h1,h2,h3,h4,ht]
    rw [hh]
    exact radicalCentral_mem_center _
  · intro hc
    have hh : (rad t ht).val ∈ highestRoot (F := F) := by
      rw [←center_map_eq_highestRoot radical₁ le_rfl (fiveRootSubgroup_le_unipotent _ _)]
      exact mem_map_of_mem _ hc
    obtain ⟨a,ha⟩ := hh
    have ha' : unipotentProduct ![a.toAdd,0,0,0,0,0] = unipotentProduct t := by
      simpa [highestRootHom,unipotentProduct,rad] using ha
    have he := unipotentProduct_injective ha'
    rw [←he]
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> rfl

private theorem normalized_radical_dichotomy (hq : 4 < Nat.card F)
    (N : Subgroup (radical₁ (F := F)))
    (hn : local₁ ≤ normalizer (N.map (radical₁ (F := F)).subtype : Set (Model F))) :
    N ≤ center (radical₁ (F := F)) ∨ N = ⊤ := by
  let W := (N.map horizontal).toAddSubgroup'
  have hmem (v : Fin 4 → F) : v ∈ W ↔
      ∃ (t : Fin 6 → F) (ht : t 5 = 0), rad t ht ∈ N ∧ ![t 1,t 2,t 3,t 4] = v := by
    change (∃ r ∈ N, horizontal r = Multiplicative.ofAdd v) ↔ _
    constructor
    · rintro ⟨r,hr,he⟩
      obtain ⟨t,ht,hv⟩ := r.property
      have hh : r = rad t ht := Subtype.ext hv.symm
      subst r
      exact ⟨t,ht,hr,by simpa [horizontal_rad] using congrArg Multiplicative.toAdd he⟩
    · rintro ⟨t,ht,hr,he⟩
      exact ⟨rad t ht,hr,by rw [horizontal_rad,he]⟩
  have hconj (g : Model F) (hg : g ∈ local₁) (r s : radical₁ (F := F))
      (hr : r ∈ N) (he : s.val = g*r.val*g⁻¹) : s ∈ N := by
    have hh := (mem_normalizer_iff.mp (hn hg) r.val).mp (mem_map_of_mem _ hr)
    rw [←he] at hh
    obtain ⟨z,hz,hze⟩ := hh
    exact (Subtype.ext hze : z = s) ▸ hz
  have hs (a b c d e : F) (hv : ![b,c,d,e] ∈ W) :
      ![b+a*c+a^2*d+a^3*e,c+a^2*e,d+a*e,e] ∈ W := by
    obtain ⟨t,ht,hr,hv⟩ := (hmem _).mp hv
    have h1 : t 1 = b := congrFun hv 0
    have h2 : t 2 = c := congrFun hv 1
    have h3 : t 3 = d := congrFun hv 2
    have h4 : t 4 = e := congrFun hv 3
    let u : Fin 6 → F := ![0,0,0,0,0,a]
    let s := unipotentProductParameters (unipotentProductParameters u t)
      (unipotentInverseParameters u)
    have hs5 : s 5 = 0 := by simp [s,u,unipotentProductParameters,unipotentInverseParameters,ht]
    have hsN : rad s hs5 ∈ N := by
      apply hconj (unipotentProduct u)
        (unipotent_le_local₁ (unipotentProduct_mem u)) (rad t ht) _ hr
      exact (by simp only [rad,s,unipotentProduct_inv,unipotentProduct_mul])
    refine (hmem _).mpr ⟨s,hs5,hsN,?_⟩
    ext i
    fin_cases i <;> simp [s,u,unipotentProductParameters,unipotentInverseParameters,
      ht,h1,h2,h3,h4,CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod] <;> ring
  have hw (b c d e : F) (hv : ![b,c,d,e] ∈ W) : ![e,d,c,b] ∈ W := by
    obtain ⟨t,ht,hr,hv⟩ := (hmem _).mp hv
    let s : Fin 6 → F := ![t 0+t 1*t 4+t 2*t 3,t 4,t 3,t 2,t 1,0]
    have hsN : rad s rfl ∈ N := by
      apply hconj weylS (mem_sup_right (subset_closure (by simp))) (rad t ht) _ hr
      exact (weylS_fiveRoot_conjugate t ht).symm
    refine (hmem _).mpr ⟨s,rfl,hsN,?_⟩
    have h1 : t 1 = b := congrFun hv 0
    have h2 : t 2 = c := congrFun hv 1
    have h3 : t 3 = d := congrFun hv 2
    have h4 : t 4 = e := congrFun hv 3
    simp [s,h1,h2,h3,h4]
  have htor (a : Fˣ) (b : F) (hv : ![b,0,0,0] ∈ W) : ![(a:F)^3*b,0,0,0] ∈ W := by
    obtain ⟨t,ht,hr,hv⟩ := (hmem _).mp hv
    let s := torusUnipotentParameters a a⁻¹ t
    have hs5 : s 5 = 0 := by simp [s,torusUnipotentParameters,ht]
    have hsN : rad s hs5 ∈ N := by
      apply hconj (torus a a⁻¹) (short_torus_mem_local₁ a)
        (rad t ht) _ hr
      exact (torus_unipotentProduct a a⁻¹ t).symm
    refine (hmem _).mpr ⟨s,hs5,hsN,?_⟩
    have h1 : t 1 = b := congrFun hv 0
    have h2 : t 2 = 0 := congrFun hv 1
    have h3 : t 3 = 0 := congrFun hv 2
    have h4 : t 4 = 0 := congrFun hv 3
    ext i
    fin_cases i <;> simp [s,torusUnipotentParameters,h1,h2,h3,h4,div_eq_mul_inv,pow_succ]
  have hcube (a b : F) (hb : ![b,0,0,0] ∈ W) : ![a^3*b,0,0,0] ∈ W := by
    by_cases ha : a=0
    · subst a
      convert W.zero_mem using 1
      ext i
      fin_cases i <;> simp
    · exact htor (Units.mk0 a ha) b hb
  rcases horizontal_dichotomy hq W hs hw hcube with hz | hall
  · left
    rw [←horizontal_ker]
    intro r hr
    have hh : (horizontal r).toAdd ∈ W := mem_map_of_mem _ hr
    rw [hz] at hh
    exact congrArg Multiplicative.ofAdd hh
  · right
    apply frattini_nongenerating
    rw [radical₁_frattini_eq_center,←horizontal_ker,←comap_map_eq]
    have he : N.map horizontal = ⊤ := Subgroup.toAddSubgroup'.injective hall
    rw [he,comap_top]



/-- Above field order four, a normal subgroup of the short local core is
central or the whole core. Normality is only required in the local factor. -/
theorem local_core_dichotomy (hq : 4 < Nat.card F)
    (N : Subgroup (local₁ (F := F))) [N.Normal]
    (hN : N ≤ pCore 2 (local₁ (F := F))) :
    N ≤ center (local₁ (F := F)) ∨ N = pCore 2 (local₁ (F := F)) := by
  let P := local₁ (F := F)
  let Q := radical₁ (F := F)
  let N0 := N.map P.subtype
  let N1 := N0.subgroupOf Q
  have hNr : N0 ≤ Q := (map_mono hN).trans_eq local₁_pCore
  have hm : N1.map Q.subtype = N0 := map_subgroupOf_eq_of_le hNr
  have hn0 : P ≤ normalizer (N0 : Set (Model F)) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      N.le_normalizer_map P.subtype
  have hn1 : P ≤ normalizer (N1.map Q.subtype : Set (Model F)) := by rwa [hm]
  rcases normalized_radical_dichotomy hq N1 hn1 with hc | ht
  · left
    have hhigh : N0 ≤ highestRoot := by
      rw [←hm,←center_map_eq_highestRoot Q le_rfl (fiveRootSubgroup_le_unipotent _ _)]
      exact map_mono hc
    intro x hx
    obtain ⟨a,ha⟩ := hhigh (mem_map_of_mem P.subtype hx)
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y : Model F)*(x : Model F) = (x : Model F)*(y : Model F)
    change rootA a.toAdd = (x : Model F) at ha
    rw [←ha]
    exact mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA a.toAdd y.property)
  · right
    apply map_injective P.subtype_injective
    change N0 = P.pCoreIn 2
    rw [local₁_pCore,←hm,ht,←MonoidHom.range_eq_map,range_subtype]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Maximal
