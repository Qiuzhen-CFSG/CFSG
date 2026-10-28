module

public import Theory.GroupTheory.ConjugationFamilyWeakClosure
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.GroupTheory.FixedPointFree
public import Theory.GroupTheory.QuaternionCentralProductSylowIndex
public import Theory.GroupTheory.QuaternionCentralProductNineAction

/-!
# Exceptional centralizers in the `L₃(4)` amalgam

These are the terminal deductions in the exceptional branch of §5.3.7,
where `q = 4` and both local quotients `Mᵢ/Vᵢ` are symmetric groups of degree
five. They do not yet assert the complete exceptional centralizer theorem.

The source's `Q₈²` is the central product of two quaternion eights, of order
32, with elementary abelian quotient of order 16 by its central involution.
The quaternion factors give an ambient order dividing 2304. Together with
a Sylow subgroup of order 128 and the normal-closure orbit bound, this forces
Sylow index nine. In the resulting quotient, an involution acting on `E₉`
without inverting it has a nonidentity fixed cubic element. Lifting that
element, weak closure forces it into the image of a two-group normalizer,
which is impossible. This proves the last contradiction without introducing
an odd residual as an additional interface.

The elementary normal-closure assertion used from B.2.14 is proved from
a normal self-centralizing core and containment in the Sylow centralizer.
For the other branches, a normal closure with center `Z(S)`, or with
centralizer `Vᵢ`, yields the desired containment by normalizer functoriality.
The order-nine action recognition is now discharged by the quaternion-product
theorem: `exceptional_quaternion_core_contradiction` needs no action witness.
The missing geometric inputs are the marked Sylow structure and the
normal-closure alternatives and orbit lower bound. In particular,
no hypothesis below identifies the desired centralizer with its proposed
local overgroup.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §5.3.7, printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter5.Section03CentralizerExceptional

/-- The elementary part of B.2.14 needed in the central quotient. -/
theorem quotient_normal_closure_elementary
    {H : Type*} [Group H] (T R Z : Subgroup H) [R.Normal]
    [IsElementaryAbelian 2 Z]
    (hRT : R ≤ T) (hself : centralizer (R : Set H) ≤ R)
    (hZ : Z ≤ centralizer (T : Set H)) :
    normalClosure (Z : Set H) ≤ R ∧
      IsElementaryAbelian 2 (normalClosure (Z : Set H)) := by
  let A := (center R).map R.subtype
  let : A.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZA : Z ≤ A := by
    intro z hz
    have hzc : z ∈ centralizer (R : Set H) := centralizer_le hRT (hZ hz)
    refine ⟨⟨z, hself hzc⟩, mem_center_iff.mpr ?_, rfl⟩
    intro r
    exact Subtype.ext (hzc r r.property)
  have hWA : normalClosure (Z : Set H) ≤ A := normalClosure_le_normal hZA
  have hAc : A ≤ centralizer (A : Set H) := by
    rintro x ⟨x, hx, rfl⟩ y ⟨y, _, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx y)
  let : IsMulCommutative (normalClosure (Z : Set H)) :=
    le_centralizer_iff_isMulCommutative.mp (hWA.trans (hAc.trans (centralizer_le hWA)))
  exact ⟨hWA.trans (map_subtype_le _), IsElementaryAbelian.normalClosure_of_isMulCommutative Z⟩

/-- The orbit lower bound rules out all indices except nine. The quaternion
central product bounds the ambient order by a divisor of 2304, and the
marked Sylow subgroup has order 128. -/
theorem index_eq_nine_of_quaternion_core
    {H : Type*} [Group H] [Finite H]
    (Q : Subgroup H) [Q.Normal]
    (hCQ : centralizer (Q : Set H) ≤ Q)
    (hZQ : Nat.card (center Q) = 2)
    (B C : Subgroup Q)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hBC : Nat.card (B ⊓ C : Subgroup Q) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤)
    (T : Sylow 2 H) (hT : Nat.card T = 128)
    (hlower : 4 ≤ (T : Subgroup H).index) :
    (T : Subgroup H).index = 9 := by
  have hd := card_dvd_of_selfCentralizing_quaternion_factors
    Q hCQ hZQ B C hB hC hBC hcomm hjoin
  have hcount := (T : Subgroup H).card_mul_index
  rw [hT] at hcount
  rw [← hcount] at hd
  have hi : (T : Subgroup H).index ∣ 18 :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 128) hd
  have hn := T.not_dvd_index
  obtain ⟨k, hk⟩ := hi
  have hkbound : k ≤ 4 := by
    have hm := Nat.mul_le_mul_right k hlower
    omega
  simp only [Nat.dvd_iff_mod_eq_zero] at hn
  interval_cases k <;> omega

/-- The local two-group bound on `C_G(z) ∩ Mᵢ` passes to the normalizer
of `Vᵢ` inside the centralizer. -/
theorem normalizer_in_centralizer_isTwoGroup
    {G : Type*} [Group G] (z : G) (V M : Subgroup G)
    (hV : V ≤ centralizer ({z} : Set G))
    (hNM : normalizer (V : Set G) ≤ M)
    (htwo : IsPGroup 2 (centralizer ({z} : Set G) ⊓ M : Subgroup G)) :
    IsPGroup 2 (normalizer (V.subgroupOf (centralizer ({z} : Set G)) :
      Set (centralizer ({z} : Set G)))) := by
  rw [← subgroupOf_normalizer_eq hV]
  have hh := (htwo.to_le (inf_le_inf_left (centralizer ({z} : Set G)) hNM)).comap_subtype
    (K := centralizer ({z} : Set G))
  change IsPGroup 2 ((centralizer ({z} : Set G) ⊓ normalizer (V : Set G)).subgroupOf
    (centralizer ({z} : Set G))) at hh
  rw [inf_subgroupOf_left] at hh
  exact hh

/-- Weak closure excludes cubic elements centralizing the image of `V` modulo
an arbitrary kernel contained in `T`, when `N(V)` is a two-group. -/
theorem quotient_centralizer_cube_eq_one
    {H K : Type*} [Group H] [Group K]
    (T V : Subgroup H) (f : H →* K) (hf : Function.Surjective f)
    (hVT : V ≤ T) (hker : f.ker ≤ T)
    (hweak : ∀ g : H, V.map (MulAut.conj g).toMonoidHom ≤ T →
      V.map (MulAut.conj g).toMonoidHom = V)
    (htwo : IsPGroup 2 (normalizer (V : Set H)))
    (r : K) (hr : r ∈ centralizer (V.map f : Set K)) (hcube : r ^ 3 = 1) :
    r = 1 := by
  obtain ⟨g, rfl⟩ := hf r
  have hn : g ∈ normalizer ((V.map f).comap f : Set H) :=
    (V.map f).le_normalizer_comap f (centralizer_le_normalizer _ hr)
  rw [comap_map_eq] at hn
  have hNV := SubgroupFusion.normalizer_le_of_weakly_closed
    (le_sup_left : V ≤ V ⊔ f.ker) (sup_le hVT hker) hweak hn
  let r' : (normalizer (V : Set H)).map f := ⟨f g, mem_map_of_mem f hNV⟩
  have hr' : r' ^ 3 = 1 := Subtype.ext hcube
  have heq : r' = 1 := (htwo.map f |>.powEquiv (by decide : Nat.Coprime 2 3)).injective
    (by change r' ^ 3 = (1 : (normalizer (V : Set H)).map f) ^ 3
        simpa only [one_pow] using hr')
  exact congrArg Subtype.val heq

/-- The remaining action test in the order-nine branch is that the involution
does not invert the whole elementary abelian three-group. -/
theorem exists_cubic_fixed_of_not_inversion
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (σ : MulAut E) (hσ : Function.Involutive σ)
    (hnot : ∃ a : E, σ a ≠ a⁻¹) :
    ∃ r : E, r ≠ 1 ∧ σ r = r ∧ r ^ 3 = 1 := by
  classical
  have hn : ¬ MonoidHom.FixedPointFree σ := by
    intro hfree
    obtain ⟨a, ha⟩ := hnot
    exact ha (congrFun (hfree.coe_eq_inv_of_involutive hσ) a)
  obtain ⟨r, hfix, hne⟩ : ∃ r : E, σ r = r ∧ r ≠ 1 := by
    by_contra h
    apply hn
    intro r hfix
    by_contra hr
    exact h ⟨r, hfix, hr⟩
  exact ⟨r, hne, hfix,
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 E) r⟩

/-- The terminal contradiction in the exceptional case. The image of `V` is
cyclic, generated by `t`, and its action on an embedded `E₉` is an involution
which is not inversion. A fixed cubic element contradicts weak closure. -/
theorem exceptional_action_contradiction
    {H K E : Type*} [Group H] [Group K] [Group E] [Finite E]
    [IsElementaryAbelian 3 E]
    (T V : Subgroup H) (f : H →* K) (hf : Function.Surjective f)
    (hVT : V ≤ T) (hker : f.ker ≤ T)
    (hweak : ∀ g : H, V.map (MulAut.conj g).toMonoidHom ≤ T →
      V.map (MulAut.conj g).toMonoidHom = V)
    (htwo : IsPGroup 2 (normalizer (V : Set H)))
    (e : E →* K) (he : Function.Injective e)
    (t : K) (hV : V.map f = zpowers t)
    (σ : MulAut E) (hσ : Function.Involutive σ)
    (haction : ∀ r : E, e (σ r) = t * e r * t⁻¹)
    (hnot : ∃ a : E, σ a ≠ a⁻¹) : False := by
  obtain ⟨r, hr, hfix, hcube⟩ := exists_cubic_fixed_of_not_inversion σ hσ hnot
  have hc : Commute t (e r) := by
    have hh := haction r
    rw [hfix] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hcV : e r ∈ centralizer (V.map f : Set K) := by
    rw [hV]
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact hc.zpow_left n
  have hone := quotient_centralizer_cube_eq_one T V f hf hVT hker hweak htwo
    (e r) hcV (by rw [← map_pow, hcube, map_one])
  exact hr (he (hone.trans (map_one e).symm))

/-- The normal-closure branch `Z(W) = Z(S)` immediately gives the desired
centralizer containment through the previously established normalizer bound. -/
theorem centralizer_le_of_normal_closure_center
    {G : Type*} [Group G] (z : G) (Z W M₁ M₂ : Subgroup G)
    (hn : centralizer ({z} : Set G) ≤ normalizer (W : Set G))
    (hcenter : (center W).map W.subtype = Z)
    (hNZ : normalizer (Z : Set G) ≤ M₁ ⊓ M₂) :
    centralizer ({z} : Set G) ≤ M₁ ⊓ M₂ := by
  apply le_trans hn
  apply le_trans (normalizer_le_normalizer_characteristic_image W (center W))
  simpa only [hcenter] using hNZ

/-- In the abelian normal-closure branch, recognizing its ambient centralizer
as `Vᵢ` forces its normalizer to normalize `Vᵢ`. The local amalgam then gives
the intersection bound. -/
theorem centralizer_le_of_normal_closure_centralizer
    {G : Type*} [Group G] (z : G) (W V M M₁ M₂ : Subgroup G)
    (hn : centralizer ({z} : Set G) ≤ normalizer (W : Set G))
    (hCV : centralizer (W : Set G) = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hlocal : centralizer ({z} : Set G) ⊓ M ≤ M₁ ⊓ M₂) :
    centralizer ({z} : Set G) ≤ M₁ ⊓ M₂ := by
  have hNM : normalizer (W : Set G) ≤ M := by
    apply le_trans (normalizer_le_normalizer_centralizer W)
    simpa only [hCV] using hNV
  exact (le_inf le_rfl (hn.trans hNM)).trans hlocal

/-- The nonabelian normal closure escaping `S` is impossible once its
quaternion structure and orbit lower bound have been established. The cubic
actor is constructed by the order-nine recognition theorem, rather than
assumed as action data. Normality and order 32 put the core in the Sylow
subgroup, as needed for the weak-closure argument. -/
theorem exceptional_quaternion_core_contradiction
    {H : Type*} [Group H] [Finite H]
    (Q : Subgroup H) [Q.Normal]
    (hQ : Nat.card Q = 32)
    (hCQ : centralizer (Q : Set H) ≤ Q)
    (hZQ : Nat.card (center Q) = 2)
    (B C : Subgroup Q)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hBC : Nat.card (B ⊓ C : Subgroup Q) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤)
    (T : Sylow 2 H) (hT : Nat.card T = 128)
    (hlower : 4 ≤ (T : Subgroup H).index)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (hVQ : Nat.card (V ⊓ Q : Subgroup H) = 8)
    (hVT : V ≤ (T : Subgroup H))
    (hweak : ∀ g : H, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup H) →
      V.map (MulAut.conj g).toMonoidHom = V)
    (htwo : IsPGroup 2 (normalizer (V : Set H))) : False := by
  have hindex := index_eq_nine_of_quaternion_core Q hCQ hZQ B C
    hB hC hBC hcomm hjoin T hT hlower
  obtain ⟨r, hr, hne, hcube⟩ :=
    exists_fixed_cubic_of_quaternion_core_sylow_index_nine Q hQ hCQ B C
      hB hC hjoin hBC hcomm T hT hindex V hV hVQ
  have hQtwo : IsPGroup 2 Q := IsPGroup.of_card (n := 5) hQ
  have hker : (QuotientGroup.mk' Q).ker ≤ (T : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact hQtwo.le_sylow_of_normal T
  exact hne (quotient_centralizer_cube_eq_one (T : Subgroup H) V
    (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
    hVT hker hweak htwo r hr hcube)

/-- A local two-group containing the marked Sylow subgroup is precisely that
Sylow subgroup. In particular the local bound used in the centralizer
argument requires only `T ≤ M₁ ∩ M₂`, not equality of the amalgam
intersection with `T`. -/
theorem centralizer_inter_le_of_isTwoGroup
    {G : Type*} [Group G] (z : G) (T : Sylow 2 G) (M M₁ M₂ : Subgroup G)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (hTinter : (T : Subgroup G) ≤ M₁ ⊓ M₂)
    (htwo : IsPGroup 2 (centralizer ({z} : Set G) ⊓ M : Subgroup G)) :
    centralizer ({z} : Set G) ⊓ M ≤ M₁ ⊓ M₂ := by
  rw [T.is_maximal' htwo (le_inf hTH hTM)]
  exact hTinter

/-- Assembly of the normal-closure branches, with the geometric alternatives
explicitly left as premises. The quaternion-core contradiction above supplies
`hescape` once the marked geometry has been proved. This reduction does not
claim to establish those geometric alternatives from quotient orders. -/
theorem centralizer_le_of_normal_closure_alternatives
    {G : Type*} [Group G] (z : G) (Z W S V₁ V₂ M₁ M₂ : Subgroup G)
    (hn : centralizer ({z} : Set G) ≤ normalizer (W : Set G))
    (hNZ : normalizer (Z : Set G) ≤ M₁ ⊓ M₂)
    (hNV₁ : normalizer (V₁ : Set G) ≤ M₁)
    (hNV₂ : normalizer (V₂ : Set G) ≤ M₂)
    (hlocal₁ : centralizer ({z} : Set G) ⊓ M₁ ≤ M₁ ⊓ M₂)
    (hlocal₂ : centralizer ({z} : Set G) ⊓ M₂ ≤ M₁ ⊓ M₂)
    (hab : IsMulCommutative W → W = Z ∨
      centralizer (W : Set G) = V₁ ∨ centralizer (W : Set G) = V₂)
    (hcenter : ¬ IsMulCommutative W → W ≤ S → (center W).map W.subtype = Z)
    (hescape : ¬ IsMulCommutative W → ¬ W ≤ S → False) :
    centralizer ({z} : Set G) ≤ M₁ ⊓ M₂ := by
  classical
  by_cases hcomm : IsMulCommutative W
  · obtain hW | hV₁ | hV₂ := hab hcomm
    · exact hn.trans (by simpa only [hW] using hNZ)
    · exact centralizer_le_of_normal_closure_centralizer z W V₁ M₁ M₁ M₂
        hn hV₁ hNV₁ hlocal₁
    · exact centralizer_le_of_normal_closure_centralizer z W V₂ M₂ M₁ M₂
        hn hV₂ hNV₂ hlocal₂
  · have hWS : W ≤ S := by
      by_contra h
      exact hescape hcomm h
    exact centralizer_le_of_normal_closure_center z Z W M₁ M₂ hn
      (hcenter hcomm hWS) hNZ

end CFSG.Quasithin.Chapter5.Section03CentralizerExceptional
