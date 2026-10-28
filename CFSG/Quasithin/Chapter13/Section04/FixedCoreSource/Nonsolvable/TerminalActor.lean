module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReturningAction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ReturningActor
/-!
# Selecting the terminal actor in the original Sylow subgroup

Identify the literal first centralizer residual under the original
augmentation action with the actual A4 point residual in S6. The model
calculation chooses an even conjugator carrying the returning
transposition into the given Sylow subgroup, with a cubic commutator
in that residual. Lift the conjugator through L/centralCore L.

The action kernel is O2(LT), contained in the original T. Thus the whole
conjugated actor lies in T, and its commutator with the original residual
cannot be a two-group. SourceContradiction applies this to the selected
component K to prove K=[K,A], and then invokes the terminal offender
argument. No model, normalization or movement callback is assumed.
Source: Aschbacher–Smith, final proof of 13.4.1, printed p.915,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates Stellmacher
open Theory.SpecificGroups.SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem core_point_residual_image
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (M : Subgroup G) (hLM : L ≤ M) (hn : M ≤ normalizer (V : Set G))
    (q : M →* Equiv.Perm (Fin 6))
    (hq : ∀ (a : M) (v : V),
      (m.coordinate (V.normalizerMonoidHom (inclusion hn a) v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (q a) (m.coordinate v).toAdd)
    (hqL : ∀ l : L, q (inclusion hLM l) =
      (m.quotient (QuotientGroup.mk' (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L) l)).val)
    (z : V) (hzL : z.val ∉ centralizer (L : Set G)) :
    ∃ a : alternatingGroup (Fin 6),
      BinaryPermutation.SixCorePoint.stabilizer (m.coordinate z).toAdd = BinaryFlags.H1.conjBy a.val ∧
      ((Solvable.firstCentralizerResidual L z.val).subgroupOf M).map q =
        BinaryFlags.K.conjBy a.val := by
  let w := (m.coordinate z).toAdd
  let C := L ⊓ centralizer ({z.val} : Set G)
  let R := Solvable.firstCentralizerResidual L z.val
  have hCM : C ≤ M := inf_le_left.trans hLM
  have hRM : R ≤ M := (Solvable.firstCentralizerResidual_le L z.val).trans hCM
  have hw : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a w = w := by
    intro hw
    exact hzL ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) _).mp hw))
  obtain ⟨a,ha⟩ := BinaryPermutation.SixCorePoint.exists_point_stabilizer w hw
  have hC : (C.subgroupOf M).map q =
      BinaryPermutation.SixCorePoint.stabilizer w ⊓ alternatingGroup (Fin 6) := by
    apply le_antisymm
    · rintro b ⟨x,hx,rfl⟩
      have hl : x.val ∈ L := hx.1
      have he := hq x z
      have hz : V.normalizerMonoidHom (inclusion hn x) z = z := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2)
      rw [hz] at he
      exact ⟨he.symm,by
        rw [show q x = (m.quotient (QuotientGroup.mk' _ ⟨x.val,hl⟩)).val from hqL ⟨x.val,hl⟩]
        exact Subtype.property _⟩
    · intro b hb
      obtain ⟨c,hc⟩ := m.quotient.surjective ⟨b,hb.2⟩
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective _ c
      have he : q (inclusion hLM l) = b := (hqL l).trans (congrArg Subtype.val hc)
      refine ⟨inclusion hLM l,⟨l.property,?_⟩,he⟩
      have hz := hq (inclusion hLM l) z
      rw [he] at hz
      have hval := congrArg Subtype.val (m.coordinate.injective
        (Multiplicative.toAdd.injective (hz.trans hb.1)))
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hval)
  have hCa : (C.subgroupOf M).map q = BinaryFlags.L1.conjBy a.val := by
    rw [hC,ha]
    change _ = (BinaryFlags.H1 ⊓ alternatingGroup (Fin 6)).map (MulAut.conj a.val).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj a.val).injective]
    congr 1
    exact (mem_normalizer_iff_map_conj_eq.mp ((alternatingGroup (Fin 6)).le_normalizer a.property)).symm
  have hRi : R.subgroupOf M =
      (pResidual 2 (C.subgroupOf M)).map (C.subgroupOf M).subtype := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hRM,map_embedded_pResidual,
      map_subgroupOf_eq_of_le hCM,core_component_point_twoResidual D m eL z hzL]
  refine ⟨a,ha,?_⟩
  rw [hRi,map_embedded_pResidual,hCa]
  exact (map_embedded_pResidual 2 BinaryFlags.L1 (MulAut.conj a.val).toMonoidHom).symm.trans
    (congrArg (map (MulAut.conj a.val).toMonoidHom) BinaryFlags.residual_L1)

/-- Conjugate an original transposition actor by an element of L into the
same T. Its commutator with the literal first residual is not a two-group,
as witnessed by an order-three element in the actual permutation image. -/
theorem core_transposition_cubic_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAM : A ≤ L ⊔ (T : Subgroup G))
    (hw : ∀ v : V, v.val ∈ ⁅V,A⁆ → v ≠ 1 → m.weight v = 2)
    (hm : ⁅V,A⁆ ≠ ⊥) :
    ∃ l ∈ L, A.conjBy l ≤ (T : Subgroup G) ∧
      ¬ IsPGroup 2 (⁅Solvable.firstCentralizerResidual L z.val,A.conjBy l⁆ : Subgroup G) := by
  let M := L ⊔ (T : Subgroup G)
  have hn : M ≤ normalizer (V : Set G) :=
    sup_le D.normalizes ((structural G T L h).2.2 V D).1
  obtain ⟨q,hq,hqL,hAlt,hker⟩ := exists_core_product_permutation D m h structural eL
  obtain ⟨t₀,ht₀,hswap,himage⟩ := core_weight_two_actor_image D m M A hn q hq hAM hw hm
  have hsurj : Function.Surjective q := by
    have hi : q.range.index ∣ 2 := by
      have hh : alternatingGroup (Fin 6) ≤ q.range := hAlt ▸ map_le_range q (L.subgroupOf M)
      simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hh
    rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
    · exact MonoidHom.range_eq_top.mp (index_eq_one.mp hi)
    · have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
      obtain ⟨a,ha⟩ := ht₀
      have ht : t₀ ∈ q.range := ⟨inclusion hAM a,ha⟩
      rw [he] at ht
      have hh := hswap.sign_eq
      rw [Equiv.Perm.mem_alternatingGroup.mp ht] at hh
      contradiction
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let P := S.mapSurjective hsurj
  obtain ⟨a,ha,hRimage⟩ := core_point_residual_image D m eL M le_sup_left hn q hq hqL z hzL
  have hP : (P : Subgroup (Equiv.Perm (Fin 6))) ≤ BinaryFlags.H1.conjBy a.val := by
    rw [←ha]
    rintro b ⟨t,ht,rfl⟩
    have hh := hq t z
    have he : V.normalizerMonoidHom (inclusion hn t) z = z := by
      apply Subtype.ext
      apply mul_inv_eq_iff_eq_mul.mpr
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.2 t.val ht
    change (m.coordinate (V.normalizerMonoidHom (inclusion hn t) z)).toAdd = _ at hh
    rw [he] at hh
    exact hh.symm
  obtain ⟨b,hb,r,hr,ho⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.ReturningActor.even_conjugate_point_actor
    P a.val t₀ hP hswap
  obtain ⟨c,hc⟩ := m.quotient.surjective b
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective _ c
  have hlq : q (inclusion (show L ≤ M from le_sup_left) l) = b.val :=
    (hqL l).trans (congrArg Subtype.val hc)
  have hA'M : A.conjBy l.val ≤ M := by
    rintro x ⟨x,hx,rfl⟩
    exact M.mul_mem (M.mul_mem (show l.val ∈ M from (show L ≤ M from le_sup_left) l.property) (hAM hx))
      (M.inv_mem ((show L ≤ M from le_sup_left) l.property))
  have hqconj (x : A) :
      q ⟨MulAut.conj l.val x.val,hA'M (mem_map_of_mem _ x.property)⟩ =
        MulAut.conj b.val ((q.comp (inclusion hAM)) x) := by
    change q ((inclusion (show L ≤ M from le_sup_left) l) * inclusion hAM x *
      (inclusion (show L ≤ M from le_sup_left) l)⁻¹) = _
    rw [map_mul,map_mul,map_inv,hlq]
    rfl
  have hAT : A.conjBy l.val ≤ (T : Subgroup G) := by
    have hkT : q.ker ≤ (S : Subgroup M) := hker ▸ pCore_isPGroup.le_sylow_of_normal S
    have hpre : ((S : Subgroup M).map q).comap q = S := by
      rw [comap_map_eq,sup_eq_left.mpr hkT]
    rintro x ⟨x,hx,rfl⟩
    have hxq : q ⟨MulAut.conj l.val x,hA'M (mem_map_of_mem _ hx)⟩ ∈ (P : Subgroup _) := by
      rw [hqconj ⟨x,hx⟩]
      apply (zpowers_le.mpr hb)
      have hx0 : (q.comp (inclusion hAM)) ⟨x,hx⟩ ∈ zpowers t₀ :=
        himage ▸ (show (q.comp (inclusion hAM)) ⟨x,hx⟩ ∈ (q.comp (inclusion hAM)).range from ⟨_,rfl⟩)
      have hh := mem_map_of_mem (MulAut.conj b.val).toMonoidHom hx0
      rwa [MonoidHom.map_zpowers] at hh
    have hxS : (⟨MulAut.conj l.val x,hA'M (mem_map_of_mem _ hx)⟩ : M) ∈ (S : Subgroup M) := by
      rw [←hpre]
      exact hxq
    exact hxS
  refine ⟨l,l.property,hAT,?_⟩
  intro hp
  let R := Solvable.firstCentralizerResidual L z.val
  let C := ⁅R,A.conjBy l.val⁆
  have hpim : IsPGroup 2 ((C.subgroupOf M).map q) := hp.comap_subtype.map q
  obtain ⟨r₀,hr₀,hrq⟩ := hRimage.symm ▸ hr
  obtain ⟨t,hqt⟩ := ht₀
  let t' : M := ⟨MulAut.conj l.val t.val,hA'M (mem_map_of_mem _ t.property)⟩
  have htq : q t' = MulAut.conj b.val t₀ := (hqconj t).trans (congrArg (MulAut.conj b.val) hqt)
  have hcomm : ⁅r,MulAut.conj b.val t₀⁆ ∈ (C.subgroupOf M).map q := by
    refine ⟨⁅r₀,t'⁆,commutator_mem_commutator hr₀ (mem_map_of_mem _ t.property),?_⟩
    rw [map_commutatorElement,hrq,htq]
  obtain ⟨n,hn⟩ := hpim.exists_orderOf_dvd_pow ⟨_,hcomm⟩
  rw [←((C.subgroupOf M).map q).orderOf_coe,ho] at hn
  have hh := Nat.prime_three.dvd_of_dvd_pow hn
  norm_num at hh
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
