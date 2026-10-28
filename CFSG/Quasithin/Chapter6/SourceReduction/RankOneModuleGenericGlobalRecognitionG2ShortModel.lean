module
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.AtlasPort.LinearGroups.G2.ShortLocalCoreCenter
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Short
public import Theory.GroupTheory.SimpleSubgroupSmallIndex

/-!
# The short G₂ core comparison in the generic diagram branch

The actual five-root radical modulo its center has four additive root
coordinates. Short-root conjugations give the cubic shear, Weyl conjugation
reverses the coordinates, and the full torus scales an isolated coordinate.
For q > 2 a nonzero invariant additive subgroup is the full coordinate space.
The center is the radical's Frattini subgroup, so a subgroup normalized by
the full short parabolic lies in that center or is the whole radical.
The center centralizes the local factor, which is the parabolic solvable
residual. At q = 2 the parabolic is solvable, using its actual SL₂ quotient
map and solvable kernel; no irreducibility is asserted in that case.

The resulting intrinsic core dichotomy is used by the adjacent generic
source extension to exclude the short endpoint for the selected diagram
factor with its two noncentral layers. The proof retains the actual octonion
carrier, root maps and full torus.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651, and F.1.12(I)(3),
printed pp.262–264 (`refs/quasithin.pdf`). Root coordinates use the existing
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
No additional ATLAS source is copied here.
-/

public noncomputable section
open Subgroup
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Short
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem horizontal_dichotomy (hq : 2 < Nat.card F)
    (W : AddSubgroup (Fin 4 → F))
    (hs : ∀ a b c d e, ![b,c,d,e] ∈ W →
      ![b+a*c+a^2*d+a^3*e,c+a^2*e,d+a*e,e] ∈ W)
    (hw : ∀ b c d e, ![b,c,d,e] ∈ W → ![e,d,c,b] ∈ W)
    (ht : ∀ a : Fˣ, ∀ b, ![b,0,0,0] ∈ W → ![(a:F)*b,0,0,0] ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset F).card < (Finset.univ : Finset F).card by
      simpa [Nat.card_eq_fintype_card] using hq)
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

private theorem normalized_radical_dichotomy (hq : 2 < Nat.card F)
    (N : Subgroup (radical₁ (F := F)))
    (hn : parabolic₁ ≤ normalizer (N.map (radical₁ (F := F)).subtype : Set (Model F))) :
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
  have hconj (g : Model F) (hg : g ∈ parabolic₁) (r s : radical₁ (F := F))
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
        (borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem u))) (rad t ht) _ hr
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
  have htor (a : Fˣ) (b : F) (hv : ![b,0,0,0] ∈ W) : ![(a:F)*b,0,0,0] ∈ W := by
    obtain ⟨t,ht,hr,hv⟩ := (hmem _).mp hv
    let s := torusUnipotentParameters a a t
    have hs5 : s 5 = 0 := by simp [s,torusUnipotentParameters,ht]
    have hsN : rad s hs5 ∈ N := by
      apply hconj (torus a a) (borel_le_parabolic₁ (mem_sup_right ⟨(a,a),rfl⟩))
        (rad t ht) _ hr
      exact (torus_unipotentProduct a a t).symm
    refine (hmem _).mpr ⟨s,hs5,hsN,?_⟩
    have h1 : t 1 = b := congrFun hv 0
    have h2 : t 2 = 0 := congrFun hv 1
    have h3 : t 3 = 0 := congrFun hv 2
    have h4 : t 4 = 0 := congrFun hv 3
    ext i
    fin_cases i <;> simp [s,torusUnipotentParameters,h1,h2,h3,h4,pow_two,mul_div_cancel_right₀ _ a.ne_zero]
  rcases horizontal_dichotomy hq W hs hw htor with hz | hall
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


/-- A subgroup normal in the full short parabolic and contained in its
actual two-core either centralizes the solvable residual or is the whole core. -/
theorem core_dichotomy_of_card_gt_two (hq : 2 < Nat.card F)
    (N : Subgroup (parabolic₁ (F := F))) [N.Normal]
    (hN : N ≤ pCore 2 (parabolic₁ (F := F))) :
    ⁅N,solvableResidual (parabolic₁ (F := F))⁆ = ⊥ ∨
      N = pCore 2 (parabolic₁ (F := F)) := by
  let P := parabolic₁ (F := F)
  let Q := radical₁ (F := F)
  let N0 := N.map P.subtype
  let N1 := N0.subgroupOf Q
  have hNr : N0 ≤ Q := (map_mono hN).trans_eq parabolic₁_pCore
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
    have hcent : N0 ≤ centralizer (local₁ (F := F) : Set (Model F)) := by
      intro x hx
      obtain ⟨a,ha⟩ := hhigh hx
      rw [mem_centralizer_iff]
      intro y hy
      rw [←ha]
      exact mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA a.toAdd hy)
    apply map_injective P.subtype_injective
    rw [map_commutator,Subgroup.map_bot,HigherFieldResiduals.parabolic₁_residual hq]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcent
  · right
    apply map_injective P.subtype_injective
    change N0 = P.pCoreIn 2
    rw [parabolic₁_pCore,←hm,ht,←MonoidHom.range_eq_map,range_subtype]


/-- The full short parabolic over the field of order two is solvable. -/
theorem parabolic_solvable_of_card_two (hF : Nat.card F = 2) :
    Group.IsSolvable (parabolic₁ (F := F)) := by
  open scoped MatrixGroups in
  have hSL : Group.IsSolvable SL(2,F) := Group.isSolvable_of_card_le_six (by
    rw [Atlas.card_sl_two,hF]
    decide)
  let := hSL
  let f := HigherParabolicRadical.Short.fullSLHom (F := F)
  let : Group.IsSolvable f.ker := HigherParabolicRadical.Short.fullSLHom_ker_solvable
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- The residual-core dichotomy at every finite binary field. The order-two
field is handled by solvability, without claiming Frattini irreducibility there. -/
theorem core_dichotomy
    (N : Subgroup (parabolic₁ (F := F))) [N.Normal]
    (hN : N ≤ pCore 2 (parabolic₁ (F := F))) :
    ⁅N,solvableResidual (parabolic₁ (F := F))⁆ = ⊥ ∨
      N = pCore 2 (parabolic₁ (F := F)) := by
  by_cases hq : 2 < Nat.card F
  · exact core_dichotomy_of_card_gt_two hq N hN
  · have he : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
    let := parabolic_solvable_of_card_two he
    left
    rw [solvableResidual_eq_bot,commutator_bot_right]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Short
