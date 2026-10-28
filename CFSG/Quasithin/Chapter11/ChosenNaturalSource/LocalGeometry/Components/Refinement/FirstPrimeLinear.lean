module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Cartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.SpecificGroups.PSL2.PrimePerfectCentralizer
public import Theory.SpecificGroups.PSL2.OddPerfectCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.GroupTheory.Hall.OddNormalProducts
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstFieldFour

/-!
# The prime-field row of the first-normalizer refinement

A component containing the original flag residual is equal to it whenever
it lies in N_G(L). For a prime-field PSL₂ two-core quotient, the full
quotient-automorphism centralizer of a nontrivial perfect seed is trivial.
The literal map of that seed kills its intrinsic two-core, so an actor
centralizing the seed quotient centralizes the containing quotient.

If L/O₂(L) is SL₃(4), its scalar center lifts to the selected Hall Cartan.
This gives a nontrivial odd subgroup X₀ centralizing both quotient actions.
The actual residual O²(X₀T) is normalized by L and K; the proved normalizer
control for LT puts K in N_G(L), forcing equality. Thus the strict prime
PSL₂ row has exactly the source exclusion of SL₃(4). The final consumer
reduces the field-four sieve to PSL₂(25), the signed ternary field-five
models and J₁, together with the completed refinement alternatives.

The only preceding geometric inputs are the original flag's inner Sylow
uniqueness, its PSL₂ quotient and the Hall Cartan. The three-row consumer
also retains the preceding L₁-centralization and faithful Cartan-line
calculation. Their producer is qt-d-1222-natural-flag-cartan, with ultimate
discharge by qt-d-1222-natural-local-geometry. The relative-components owner
retains the remaining embedding classification, local sieve and triangle.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed pp.761--762, especially the O²(X₁T) argument on p.762.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_le_quotient_kernel
    (T : Sylow 2 G) (A X : Subgroup G)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hX : X ≤ Closure.coreQuotientCentralizer A) :
    (pResidual 2 (X ⊔ (T : Subgroup G) : Subgroup G)).map (X ⊔ (T : Subgroup G)).subtype ≤
      Closure.coreQuotientCentralizer A := by
  let J := X ⊔ (T : Subgroup G)
  have hn : J ≤ normalizer (A : Set G) :=
    sup_le (hX.trans (map_subtype_le _)) hTA
  let a := (Closure.coreQuotientAction A).comp (inclusion hn)
  have hk : X.subgroupOf J ≤ a.ker := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hX hx
    have hyx : y = inclusion hn x := Subtype.ext he
    change inclusion hn x ∈ (Closure.coreQuotientAction A).ker
    exact hyx ▸ hy
  have hs : X.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hr : a.range = ((T : Subgroup G).subgroupOf J).map a := by
    rw [MonoidHom.range_eq_map, ← hs, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr hk, bot_sup_eq]
  have hp : IsPGroup 2 a.range := by
    rw [hr]
    exact T.isPGroup'.comap_subtype.map a
  have hres := pResidual_le_ker_of_isPGroup 2 a.rangeRestrict hp
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨inclusion hn x, ?_, rfl⟩
  exact congrArg Subtype.val (hres hx)

private theorem residual_normalized_of_quotient_kernel
    (T : Sylow 2 G) (A X : Subgroup G)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hX : X ≤ Closure.coreQuotientCentralizer A) :
    A ≤ normalizer ((pResidual 2 (X ⊔ (T : Subgroup G) : Subgroup G)).map
      (X ⊔ (T : Subgroup G)).subtype : Set G) := by
  let J := X ⊔ (T : Subgroup G)
  have hcT : A.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hc := pCoreIn_mono_of_normalizes (p := 2) (Y := A)
      (L := A ⊔ (T : Subgroup G)) le_sup_left (sup_le A.le_normalizer hTA)
    apply hc.trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (A ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  apply normalizes_residual_of_commutator_le_two A J J (A.pCoreIn 2)
    J.le_normalizer (hcT.trans le_sup_right) (isPGroup_pCoreIn 2 A)
    (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  rw [commutator_comm]
  exact commutator_le.mpr fun x hx a ha =>
    Closure.coreQuotientCentralizer_commutator (residual_le_quotient_kernel T A X hTA hX hx) ha

private theorem relative_component_eq_of_normal_nonsolvable
    {H A K : Subgroup G} (hK : Source.ComponentIn H K)
    (hAK : A ≤ K) (hKA : K ≤ normalizer (A : Set G))
    (hA : ¬ Group.IsSolvable A) : A = K := by
  let B := K.subgroupOf H
  let C := (A.subgroupOf H).subgroupOf B
  have hAH := hAK.trans hK.1
  have hAB : A.subgroupOf H ≤ B := comap_mono hAK
  have hn : C.Normal := normal_subgroupOf_of_le_normalizer (by
    rw [← subgroupOf_normalizer_eq hAH]
    exact comap_mono hKA)
  have ht : C = ⊤ := by
    by_contra hne
    let := hK.2.isSolvable_of_subnormal_lt_top hn.isSubnormal hne
    let e : C ≃* A := (subgroupOfEquivOfLe hAB).trans (subgroupOfEquivOfLe hAH)
    exact hA (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  apply le_antisymm hAK
  intro k hk
  exact (subgroupOf_eq_top.mp ht) (show (⟨k,hK.1 hk⟩ : H) ∈ B from hk)

omit [Finite G] in
private theorem core_kernel_of_commutator {B X : Subgroup G}
    (hXN : X ≤ normalizer (B : Set G)) (hc : ⁅X,B⁆ ≤ B.pCoreIn 2) :
    X ≤ Closure.coreQuotientCentralizer B := by
  intro x hx
  refine ⟨⟨x,hXN hx⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
  apply MulEquiv.ext
  intro z
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
  rw [Closure.coreQuotientAction_apply_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  obtain ⟨k,hk,he⟩ := hc (commutator_mem_commutator hx b.property)
  have he' : k = B.normalizerMonoidHom ⟨x,hXN hx⟩ b / b := by
    apply Subtype.ext
    simpa only [subtype_apply, div_eq_mul_inv, coe_mul, coe_inv,
      normalizerMonoidHom_apply_apply_coe, commutatorElement_def] using he
  exact he' ▸ hk

omit [Finite G] in
private theorem core_kernel_restrict {A B X : Subgroup G}
    (hBA : B ≤ A) (hXN : X ≤ normalizer (B : Set G))
    (hX : X ≤ Closure.coreQuotientCentralizer A) : X ≤ Closure.coreQuotientCentralizer B := by
  apply core_kernel_of_commutator hXN
  apply (le_inf (le_normalizer_iff_commutator_le_right.mp hXN) ?_).trans
    (inf_pCoreIn_le_of_le 2 hBA)
  exact commutator_le.mpr fun x hx b hb =>
    Closure.coreQuotientCentralizer_commutator (hX hx) (hBA hb)

private theorem odd_central_le_hall {A : Type*} [Group A] [Finite A]
    (Y Z : Subgroup A) (hY : IsHallSubgroup OddHall.oddPrimes Y)
    (hZ : Odd (Nat.card Z)) (hc : Z ≤ center A) : Z ≤ Y := by
  have hn : Z ≤ normalizer (Y : Set A) := hc.trans (center_le_normalizer _)
  have hi : Y.relIndex Z ∣ Y.index := by
    rw [← OddHall.relIndex_normalized_sup Y Z hn]
    exact relIndex_dvd_index_of_le le_sup_left
  have hcop : Nat.Coprime (Nat.card Z) Y.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpZ hpY
    have hp2 : p = 2 := Classical.not_not.mp (hY.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpY)
    subst p
    exact hZ.not_two_dvd_nat hpZ
  exact relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card _ _) hi)

open scoped MatrixGroups commutatorElement in
/-- A nonsolvable perfect seed determines the quotient-action kernel of a
prime-field PSL₂ containing group. Its intrinsic two-core is killed by the
literal map into the odd-field quotient. -/
private theorem primeLinear_quotient_kernel_control
    {B K X : Subgroup G} [Group.IsPerfect B]
    (hB : ¬ Group.IsSolvable B) (hBK : B ≤ K)
    (hXN : X ≤ normalizer (K : Set G))
    (hXB : X ≤ Closure.coreQuotientCentralizer B)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    X ≤ Closure.coreQuotientCentralizer K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  let bq : B →* Q := q.comp (inclusion hBK)
  let φ : B →* MulAut Q := (MulAut.conj : Q →* MulAut Q).comp bq
  have hz : center Q = ⊥ := by
    apply bot_unique
    intro a ha
    apply e.map_eq_one_iff.mp
    exact (GorensteinWalter.psl2_center_eq_bot F).le ((centerCongr e) ⟨a,ha⟩).property
  have hi := Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hφ : φ.range ≠ ⊥ := by
    intro he
    have hb (b : B) : inclusion hBK b ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply hi
      exact (he.le (MonoidHom.mem_range.mpr ⟨b,rfl⟩)).trans (map_one _).symm
    let j : B →* pCore 2 K := (inclusion hBK).codRestrict _ hb
    let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
    exact hB (Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro b c he
      exact (inclusion_injective hBK) (congrArg Subtype.val he)))
  have hc := Theory.PSL2.prime_field_automorphism_centralizer_eq_bot_of_perfect
    hlarge hF e φ.range hφ
  have hcore := Theory.PSL2.odd_perfect_hom_twoCore_le_ker
    (hF.symm ▸ hp.odd_of_ne_two (by omega)) (e.toMonoidHom.comp bq)
  intro x hx
  let a := Closure.coreQuotientAction K ⟨x,hXN hx⟩
  have hfix (b : B) : a (bq b) = bq b := by
    obtain ⟨r,hr,he⟩ := Closure.coreQuotientCentralizer_commutator (hXB hx) b.property
    have hq : bq r = 1 := e.injective ((hcore hr).trans (map_one e).symm)
    have he' : inclusion hBK r =
        K.normalizerMonoidHom ⟨x,hXN hx⟩ (inclusion hBK b) * (inclusion hBK b)⁻¹ :=
      Subtype.ext he
    change q (inclusion hBK r) = 1 at hq
    rw [he',map_mul,map_inv] at hq
    change Closure.coreQuotientAction K ⟨x,hXN hx⟩ (q (inclusion hBK b)) = q (inclusion hBK b)
    rw [Closure.coreQuotientAction_apply_mk]
    exact mul_inv_eq_one.mp hq
  have ha : a ∈ centralizer (φ.range : Set (MulAut Q)) := by
    rintro _ ⟨b,rfl⟩
    apply MulEquiv.ext
    intro z
    change bq b * a z * (bq b)⁻¹ = a (bq b * z * (bq b)⁻¹)
    rw [map_mul,map_mul,map_inv,hfix]
  refine ⟨⟨x,hXN hx⟩, ?_, rfl⟩
  exact hc.le ha

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
    (S : D.NonbinaryNaturalInput) {c : Coordinates D S.field} (f : InvariantFlag c)

open scoped MatrixGroups in
include c in
private theorem cartan_scalar_kernel_ne_bot {X : Subgroup G} (hX : IsCartan T L X)
    (hSL : Source.IsSL (L ⧸ pCore 2 L) 3 4) :
    X ⊓ Closure.coreQuotientCentralizer L ≠ ⊥ := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hSL
  have hc : Nat.card (center c.ModelGroup) = 3 := by
    rw [Nat.card_congr (centerCongr (c.groupEquiv.symm.trans e)).toEquiv,
      ← Matrix.PSL3.projection_ker, Matrix.PSL3.card_projectionKernel, hF]
    decide
  let N := normalizer (c.modelSylow : Set c.ModelGroup)
  let Y := (X.subgroupOf (cartanNormalizer T L)).map c.cartanProjection
  let Z := (center c.ModelGroup).subgroupOf N
  have hY : IsHallSubgroup OddHall.oddPrimes Y := by
    refine ⟨fun p hp => hX.2.p_in_pi_of_p_dvd_card p
      (hp.trans ((X.subgroupOf (cartanNormalizer T L)).card_map_dvd c.cartanProjection)), ?_⟩
    intro p hp
    exact hX.2.p_in_pi_of_p_dvd_index p
      (hp.trans (index_map_dvd _ c.cartanProjection_surjective))
  have hZ : Odd (Nat.card Z) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (center_le_normalizer _)).toEquiv, hc]
    decide
  have hZc : Z ≤ center N := by
    intro z hz
    exact mem_center_iff.mpr fun n => Subtype.ext (mem_center_iff.mp hz n)
  have hzY := odd_central_le_hall Y Z hY hZ hZc
  have hne : center c.ModelGroup ≠ ⊥ := by
    intro he
    rw [he, Nat.card_unique] at hc
    contradiction
  obtain ⟨z,hz,hzne⟩ := (center c.ModelGroup).bot_or_exists_ne_one.resolve_left hne
  have hzN : z ∈ N := center_le_normalizer _ hz
  obtain ⟨x,hx,he⟩ := hzY (show (⟨z,hzN⟩ : N) ∈ Z from hz)
  have hxz := (c.cartanProjection_coe x).symm.trans (congrArg Subtype.val he)
  have hxl : (x : G) ∈ L := x.property.1
  have hxC : (x : G) ∈ Closure.coreQuotientCentralizer L := by
    refine ⟨⟨x,L.le_normalizer hxl⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    apply MulEquiv.ext
    intro u
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) u
    rw [Closure.coreQuotientAction_apply_mk]
    apply c.groupEquiv.injective
    change c.quotientMap ((⟨x,hxl⟩ : L) * l * (⟨x,hxl⟩ : L)⁻¹) = c.quotientMap l
    rw [map_mul,map_mul,map_inv,hxz,← mem_center_iff.mp hz (c.quotientMap l),mul_inv_cancel_right]
  intro hzero
  have hx1 : (x : G) = 1 := hzero.le ⟨hx,hxC⟩
  have hx1' : (⟨x,hxl⟩ : L) = 1 := Subtype.ext hx1
  exact hzne (hxz.symm.trans (by rw [hx1',map_one]))

/-- A containing component lying in the original component normalizer is the
original flag residual. This supplies the source's strict-case escape from M. -/
theorem flag_component_eq_of_le_component_normalizer (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K : Subgroup G}
    (hK : Source.ComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hKM : K ≤ normalizer (L : Set G)) : f.Li i = K := by
  apply relative_component_eq_of_normal_nonsolvable hK hLK ?_
    (Chapter1.mem_L_not_isSolvable (flag_mem_local_of_model D S f i hm))
  exact ((le_inf hKM (hK.1.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

include D S in
/-- The literal residual O²(X₁T), for a nontrivial odd X₁, forces K into M
when X₁ centralizes both original two-core quotients. -/
theorem component_le_normalizer_of_common_quotient_kernel
    {K X₁ : Subgroup G} (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hXL : X₁ ≤ L) (hodd : Odd (Nat.card X₁)) (hne : X₁ ≠ ⊥)
    (hCL : X₁ ≤ Closure.coreQuotientCentralizer L)
    (hCK : X₁ ≤ Closure.coreQuotientCentralizer K) : K ≤ normalizer (L : Set G) := by
  let J := X₁ ⊔ (T : Subgroup G)
  let Y : Subgroup G := (pResidual 2 J).map J.subtype
  have hXY : X₁ ≤ Y := by
    intro x hx
    let x' : J := ⟨x,mem_sup_left hx⟩
    have hc : Nat.Coprime 2 (orderOf x') := by
      have he : orderOf x' = orderOf (⟨x,hx⟩ : X₁) :=
        (orderOf_coe x').symm.trans (orderOf_coe (⟨x,hx⟩ : X₁))
      rw [he]
      exact hodd.coprime_two_left.of_dvd_right (orderOf_dvd_natCard _)
    exact ⟨x',mem_pResidual_of_orderOf_coprime hc,rfl⟩
  have hY : Y ≠ ⊥ := fun he => hne (bot_unique (hXY.trans_eq he))
  have hJY : J ≤ normalizer (Y : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pResidual 2 J))
  have hLY : L ≤ normalizer (Y : Set G) :=
    residual_normalized_of_quotient_kernel T L X₁ D.sylow_normalizes_component hCL
  have hNY := D.normal_subgroup_normalizer_le S.source.toHypothesis1221
    ((map_subtype_le _).trans (sup_le_sup_right hXL _)) hY
    (sup_le hLY (le_sup_right.trans hJY))
  exact (residual_normalized_of_quotient_kernel T K X₁ hTK hCK).trans hNY

/-- The actual flag consumer of the residual argument, including the strict
first-normalizer exclusion used in source 11.1.2. -/
theorem flag_component_eq_of_common_quotient_kernel (i : Fin 2)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K X₁ : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) (hXL : X₁ ≤ L) (hodd : Odd (Nat.card X₁)) (hne : X₁ ≠ ⊥)
    (hCL : X₁ ≤ Closure.coreQuotientCentralizer L)
    (hCK : X₁ ≤ Closure.coreQuotientCentralizer K) : f.Li i = K := by
  have hTK := (f.invariant i.castSucc).trans
    ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  exact flag_component_eq_of_le_component_normalizer D S f i hm hK.1 hLK
    (component_le_normalizer_of_common_quotient_kernel D S hTK hXL hodd hne hCL hCK)

/-- In a prime-field PSL₂ row the original SL₃(4) model forces equality.
The scalar Cartan subgroup is constructed from the literal Hall subgroup,
so no centralization callback or extra hypothesis on K's action remains. -/
theorem flag_component_eq_of_primeLinear_of_linearThree (i : Fin 2)
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li i ⧸ pCore 2 (f.Li i)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi i.castSucc : Set G)) K)
    (hLK : f.Li i ≤ K) {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p)
    (hSL : Source.IsSL (L ⧸ pCore 2 L) 3 4) : f.Li i = K := by
  let X₀ := X ⊓ Closure.coreQuotientCentralizer L
  have hxN := f.cartan_normalizes hu hX i.castSucc
  have hxK := hxN.trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  have hxA : X ≤ normalizer (f.Li i : Set G) :=
    ((le_inf ((hX.1.trans inf_le_left).trans L.le_normalizer)
      (hxN.trans (normalizer _).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  have hcA : X₀ ≤ Closure.coreQuotientCentralizer (f.Li i) :=
    core_kernel_restrict ((localResidual_le _).trans inf_le_left)
      (inf_le_left.trans hxA) inf_le_right
  let : Group.IsPerfect (f.Li i) := localResidual_perfect _
  have hcK : X₀ ≤ Closure.coreQuotientCentralizer K :=
    primeLinear_quotient_kernel_control
      (Chapter1.mem_L_not_isSolvable (flag_mem_local_of_model D S f i hm))
      hLK (inf_le_left.trans hxK) hcA hp hlarge hk
  apply flag_component_eq_of_common_quotient_kernel D S f i hm hK hLK
    (inf_le_left.trans (hX.1.trans inf_le_left))
    (Odd.of_dvd_nat hX.odd (card_dvd_of_le (show X₀ ≤ X from inf_le_left)))
    (cartan_scalar_kernel_ne_bot D S (c := c) hX hSL) inf_le_right hcK

/-- The complete prime-field row of the first-normalizer refinement,
including exclusion of the original SL₃(4) model in the strict case. -/
theorem first_refinement_of_primeLinear
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K) (hfour : S.field.degree = 2)
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  by_cases he : f.Li 0 = K
  · exact .equal (by simpa using he)
  · have hl : 11 ≤ p := by rcases hp with ⟨hp,h5,h8⟩; omega
    exact .psl2 rfl hfour p hp.1 hl hk (fun hSL => he
      (flag_component_eq_of_primeLinear_of_linearThree D S f 0 hu hm hX hK hLK
        hp.1 (by omega) hk hSL))

/-- Apply the prime-field argument to the previously reduced field-four
sieve. Only the square-field, signed ternary and J₁ rows remain. -/
theorem first_fieldFour_refinement_or_three_rows_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hfour : S.field.degree = 2) (hk : FieldFourOvergroup (K ⧸ pCore 2 K)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 25 ∨
      (∃ u, Chapter1.Section02.LocalModels.IsPSLSign (K ⧸ pCore 2 K) u 3 5 ∨
        Chapter1.Section02.LocalModels.IsSLSign (K ⧸ pCore 2 K) u 3 5) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rcases first_fieldFour_refinement_or_four_rows_of_cartan D S f hu hm hfix hX hK hLK
    hXcard hfaith hfour hk with h | ⟨p,hp,hpK⟩ | h | h | h
  · exact .inl h
  · exact .inl (first_refinement_of_primeLinear D S f hu hm hX hK hLK hfour hp hpK)
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
