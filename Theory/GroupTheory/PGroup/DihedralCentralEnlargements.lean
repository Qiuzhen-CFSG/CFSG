module
public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.SylowNormalizedResidual

/-!
# Normalizing maximal elementary subgroups in dihedral central enlargements

An automorphism of D₈ × E, for E elementary abelian, permutes precisely two
largest elementary subgroups. Every two-residual therefore fixes each one.
For a family of such central enlargements permuted by a Sylow two-subgroup T,
the pointwise normalizer kernel preserves any T-invariant elementary V generated
by its largest intersections with the family. The residual–Sylow supplement
proves the full kernel assertion.

This is the kernel argument on Γ in Aschbacher–Smith 10.2.1, printed p.743.
It does not assume the normalizer containment or the final action conclusion.
-/
public section
open Subgroup SymmetricFourWreath
open scoped IsMulCommutative
namespace DihedralCentralEnlargements
private abbrev Model (E : Type*) := D8 × E
private def family (E : Type*) [Group E] (i : Bool) : Subgroup (Model E) := (plane i).prod ⊤
private theorem elementary_plane (A : Subgroup D8) (hA : IsElementaryAbelian 2 A) :
    ∃ i, A ≤ plane i := by
  by_cases ht : A ≤ plane true
  · exact ⟨true,ht⟩
  obtain ⟨x,hx,hxt⟩ := SetLike.not_le_iff_exists.mp ht
  refine ⟨false,?_⟩
  intro y hy
  have hlocal : ∀ x y : D8, x^2=1 → y^2=1 → x*y=y*x → x∉plane true → y∈plane false := by
    decide +kernel
  let : IsElementaryAbelian 2 A := hA
  exact hlocal x y (elemPow_eq_one_of_isElementaryAbelian x hx)
    (elemPow_eq_one_of_isElementaryAbelian y hy)
    (congrArg Subtype.val (hA.is_comm.comm (⟨x,hx⟩ : A) ⟨y,hy⟩)) hxt
variable (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
omit [Finite E] [IsElementaryAbelian 2 E] in
private theorem elementary_cover (A : Subgroup (Model E)) (hA : IsElementaryAbelian 2 A) :
    ∃ i, A ≤ family E i := by
  let : IsElementaryAbelian 2 A := hA
  obtain ⟨i,hi⟩ := elementary_plane (A.map (MonoidHom.fst D8 E)) (IsElementaryAbelian.map _)
  exact ⟨i,fun x hx => ⟨hi (mem_map_of_mem _ hx),mem_top _⟩⟩
omit [Finite E] [IsElementaryAbelian 2 E] in
private theorem family_card (i : Bool) : Nat.card (family E i) = 4 * Nat.card E := by
  rw [family,Nat.card_congr (prodEquiv (plane i) (⊤ : Subgroup E)).toEquiv,
    Nat.card_prod,card_plane,Nat.card_congr (topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv]
private instance family_elementary (i : Bool) : IsElementaryAbelian 2 (family E i) where
  is_comm.comm := by
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x.1.1,x.2.1⟩ : plane i) ⟨y.1.1,y.2.1⟩)
    · exact IsMulCommutative.is_comm.comm _ _
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Subtype.ext
    exact Prod.ext (elemPow_eq_one_of_isElementaryAbelian x.1.1 x.2.1)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) x.1.2))
omit [Finite E] in
private theorem family_injective : Function.Injective (family E) := by
  intro i j he
  have h : ∀ x : D8,x ∈ plane i ↔ x ∈ plane j := by
    intro x
    have hh := SetLike.ext_iff.mp he (x,1)
    simpa only [family,mem_prod,mem_top,and_true] using hh
  have hcheck : ∀ a b : Bool,(∀ x : D8,x ∈ plane a ↔ x ∈ plane b) → a=b := by decide +kernel
  exact hcheck i j h
private theorem exists_family_image (a : MulAut (Model E)) (i : Bool) :
    ∃ j : Bool,(family E i).map a.toMonoidHom = family E j := by
  obtain ⟨j,hj⟩ := elementary_cover E ((family E i).map a.toMonoidHom)
    (IsElementaryAbelian.map a.toMonoidHom)
  refine ⟨j,eq_of_le_of_card_ge hj ?_⟩
  rw [card_map_of_injective a.injective,family_card,family_card]
private noncomputable def familyMap (a : MulAut (Model E)) (i : Bool) : Bool :=
  Classical.choose (exists_family_image E a i)
private theorem familyMap_spec (a : MulAut (Model E)) (i : Bool) :
    (family E i).map a.toMonoidHom = family E (familyMap E a i) :=
  Classical.choose_spec (exists_family_image E a i)
private theorem familyMap_injective (a : MulAut (Model E)) : Function.Injective (familyMap E a) := by
  intro i j he
  apply family_injective E
  apply map_injective (f := a.toMonoidHom) a.injective
  rw [familyMap_spec,familyMap_spec,he]
private noncomputable def familyAction : MulAut (Model E) →* Equiv.Perm Bool where
  toFun a := Equiv.ofBijective (familyMap E a)
    ⟨familyMap_injective E a,Finite.surjective_of_injective (familyMap_injective E a)⟩
  map_one' := by
    apply Equiv.ext
    intro i
    apply family_injective E
    exact (familyMap_spec E 1 i).symm.trans (by ext x; simp)
  map_mul' a b := by
    apply Equiv.ext
    intro i
    apply family_injective E
    change family E (familyMap E (a*b) i) = family E (familyMap E a (familyMap E b i))
    rw [←familyMap_spec,←familyMap_spec,←familyMap_spec,map_map]
    rfl
private theorem familyAction_spec (a : MulAut (Model E)) (i : Bool) :
    (family E i).map a.toMonoidHom = family E (familyAction E a i) := familyMap_spec E a i
private theorem model_preserves {H : Type*} [Group H] (φ : H →* MulAut (Model E))
    (Q : Subgroup (Model E)) [IsElementaryAbelian 2 Q]
    (hc : Nat.card Q = 4 * Nat.card E) (h : H) (hh : h ∈ pResidual 2 H) :
    Q.map (φ h).toMonoidHom = Q := by
  obtain ⟨i,hi⟩ := elementary_cover E Q inferInstance
  have hQ : Q = family E i := eq_of_le_of_card_ge hi (by rw [hc,family_card])
  have hp : IsPGroup 2 (Equiv.Perm Bool) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    decide)
  have hk := pResidual_le_ker_of_isPGroup 2 ((familyAction E).comp φ) hp hh
  change familyAction E (φ h) = 1 at hk
  rw [hQ,familyAction_spec,hk]
  rfl
end DihedralCentralEnlargements
namespace DihedralCentralEnlargements
variable {P E H : Type*} [Group P] [Group E] [Group H] [Finite E]
  [IsElementaryAbelian 2 E]
/-- The two-residual of an actor fixes each elementary subgroup of largest order. -/
theorem pResidual_preserves
    (e : P ≃* DihedralGroup 4 × E) (φ : H →* MulAut P)
    (Q : Subgroup P) [IsElementaryAbelian 2 Q]
    (hc : Nat.card Q = 4 * Nat.card E) (h : H) (hh : h ∈ pResidual 2 H) :
    Q.map (φ h).toMonoidHom = Q := by
  let φ' := (MulAut.congr e).toMonoidHom.comp φ
  let Q' := Q.map e.toMonoidHom
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.map e.toMonoidHom
  have hcard : Nat.card Q' = 4 * Nat.card E := by
    change Nat.card (Q.map e.toMonoidHom) = _
    rw [card_map_of_injective e.injective,hc]
  have he := model_preserves E φ' Q' hcard h hh
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_map]
  have hcomp : e.toMonoidHom.comp (φ h).toMonoidHom =
      (φ' h).toMonoidHom.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change e (φ h x) = e (φ h (e.symm (e x)))
    rw [e.symm_apply_apply]
  rw [hcomp,←map_map]
  exact he
end DihedralCentralEnlargements
namespace Subgroup
variable {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
  [IsElementaryAbelian 2 E]
/-- The literal residual action fixes a largest elementary subgroup in a
central enlargement of a dihedral factor. -/
theorem pResidual_normalizes_maximal_elementary_of_dihedral
    (K F A : Subgroup G) (e : F ≃* DihedralGroup 4 × E)
    (hKF : K ≤ normalizer (F : Set G)) (hAF : A ≤ F)
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 4 * Nat.card E) :
    (pResidual 2 K).map K.subtype ≤ normalizer (A : Set G) := by
  let φ : K →* MulAut F := F.normalizerMonoidHom.comp (inclusion hKF)
  let Q := A.subgroupOf F
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hAF).toMonoidHom (subgroupOfEquivOfLe hAF).injective
  have hc : Nat.card Q = 4 * Nat.card E := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAF).toEquiv,hcard]
  rintro _ ⟨k,hk,rfl⟩
  have hh := DihedralCentralEnlargements.pResidual_preserves e φ Q hc k hk
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj (k : G)).injective])
  rintro _ ⟨a,ha,rfl⟩
  have hqa : φ k (⟨a,hAF ha⟩ : F) ∈ Q := by
    rw [←hh]
    exact mem_map_of_mem _ ha
  exact hqa
end Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {ι : Type*}
/-- The pointwise normalizer of a subgroup family is normalized by every
actor permuting the family. -/
theorem normalizes_iInf_normalizer_of_permutes
    (T : Subgroup G) (F : ι → Subgroup G)
    (hTF : ∀ t ∈ T, ∀ i, ∃ j, (F i).map (MulAut.conj t).toMonoidHom = F j) :
    T ≤ normalizer ((⨅ i, normalizer (F i : Set G) : Subgroup G) : Set G) := by
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj t).injective])
  rintro _ ⟨k,hk,rfl⟩
  apply mem_iInf.mpr
  intro i
  obtain ⟨j,hj⟩ := hTF t⁻¹ (T.inv_mem ht) i
  have he : (F j).map (MulAut.conj t).toMonoidHom = F i := by
    rw [←hj,map_map]
    have hid : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t⁻¹).toMonoidHom =
        MonoidHom.id G := by ext x; simp [MulAut.conj_apply,mul_assoc]
    rw [hid,map_id]
  rw [←he]
  exact (F j).le_normalizer_map (MulAut.conj t).toMonoidHom
    (mem_map_of_mem _ (mem_iInf.mp hk j))

/-- If a Sylow-invariant elementary group is generated by its largest
intersections with dihedral central enlargements, the pointwise kernel on
those enlargements normalizes it. -/
theorem iInf_normalizer_le_of_dihedral_elementary_family
    (T : Sylow 2 G) (V : Subgroup G) [IsElementaryAbelian 2 V]
    (F : ι → Subgroup G) (E : ι → Type*) [∀ i, Group (E i)]
    [∀ i, Finite (E i)] [∀ i, IsElementaryAbelian 2 (E i)]
    (e : ∀ i, F i ≃* DihedralGroup 4 × E i)
    (hTF : ∀ t ∈ (T : Subgroup G), ∀ i,
      ∃ j, (F i).map (MulAut.conj t).toMonoidHom = F j)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hcard : ∀ i, Nat.card (V ⊓ F i : Subgroup G) = 4 * Nat.card (E i))
    (hspan : (⨆ i, V ⊓ F i) = V) :
    (⨅ i, normalizer (F i : Set G)) ≤ normalizer (V : Set G) := by
  let K : Subgroup G := ⨅ i, normalizer (F i : Set G)
  have hres : (pResidual 2 K).map K.subtype ≤ normalizer (V : Set G) := by
    rw [←hspan]
    apply (le_iInf fun i => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
    let : IsElementaryAbelian 2 (V ⊓ F i : Subgroup G) :=
      IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
    exact pResidual_normalizes_maximal_elementary_of_dihedral K (F i) (V ⊓ F i)
      (e i) (iInf_le _ i) inf_le_right (hcard i)
  exact (le_embedded_pResidual_sup_sylow_of_normalizes T K
    (normalizes_iInf_normalizer_of_permutes (T : Subgroup G) F hTF)).trans (sup_le hres hTV)
end Subgroup
