module
public import Theory.GroupTheory.CoreInvolutionFusion
public import Theory.GroupTheory.NilpotentCommutingFamily
public import Theory.ElementaryAbelian.Basic
/-!
# Elementary conjugacy-class closure in two-groups

An involution normalizing a nontrivial elementary abelian two-subgroup fixes
one of its nonidentity elements. If this forces every normalizing member of
an ambient conjugacy class into that subgroup, the normalizer condition
extends the same assertion to the containing two-group. Sylow conjugacy
then compares this elementary class closure with a nonabelian class-generated
subgroup in another element centralizer.

Source application: Aschbacher–Smith, Lemma 2.4.24(2), odd half-degree branch,
printed p.540. The separate normal-core lemma transports the original
involution-fusion closure into a centralizer containing the ambient Sylow.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

theorem exists_nonidentity_fixed_of_elementary_normalizer
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hV : V ≠ ⊥)
    (t : G) (ht : t ^ 2 = 1) (htV : t ∈ normalizer (V : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ Commute t v := by
  obtain ⟨w, hw, hw1⟩ := (V.bot_or_exists_ne_one).resolve_left hV
  let a := MulAut.conj t
  have haV : a w ∈ V := (mem_normalizer_iff.mp htV w).mp hw
  have haa (y : G) : a (a y) = y := by
    change t * (t * y * t⁻¹) * t⁻¹ = y
    have htt : t*t=1 := by simpa only [pow_two] using ht
    have hi : t⁻¹=t := inv_eq_of_mul_eq_one_left htt
    rw [hi]
    calc
      t * (t * y * t) * t = (t*t)*y*(t*t) := by group
      _ = y := by rw [htt,one_mul,mul_one]
  by_cases hf : a w = w
  · exact ⟨w,hw,hw1,mul_inv_eq_iff_eq_mul.mp hf⟩
  refine ⟨w*a w,V.mul_mem hw haV,?_,?_⟩
  · intro he
    apply hf
    have hw2 : w*w=1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) w hw
    calc
      a w = w*(w*a w) := by rw [←mul_assoc,hw2,one_mul]
      _ = w := by rw [he,mul_one]
  · apply mul_inv_eq_iff_eq_mul.mp
    change a (w*a w) = w*a w
    rw [map_mul,haa]
    exact congrArg Subtype.val (mul_comm (⟨a w,haV⟩:V) ⟨w,hw⟩)

theorem class_mem_of_elementary_centralizer_control
    [Finite G] (P V : Subgroup G) (hP : IsPGroup 2 P)
    [IsElementaryAbelian 2 V] (hV : V ≠ ⊥) (hVP : V ≤ P)
    (u : G) (hu : orderOf u = 2)
    (hclass : ∀ v ∈ V, v ≠ 1 → IsConj u v)
    (hcontrol : ∀ v ∈ V, v ≠ 1 → ∀ t ∈ P, IsConj u t → Commute t v → t ∈ V) :
    ∀ t ∈ P, IsConj u t → t ∈ V := by
  let N := P ⊓ normalizer (V : Set G)
  have hVN : V ≤ N := le_inf hVP V.le_normalizer
  have hinside : ∀ t ∈ N, IsConj u t → t ∈ V := by
    intro t ht htu
    have ht2 : t^2=1 := by
      obtain ⟨g,rfl⟩ := isConj_iff.mp htu
      change (MulAut.conj g u)^2=1
      rw [←map_pow,←hu,pow_orderOf_eq_one,map_one]
    obtain ⟨v,hv,hv1,hcomm⟩ := exists_nonidentity_fixed_of_elementary_normalizer V hV t ht2 ht.2
    exact hcontrol v hv hv1 t ht.1 htu hcomm
  have hgen : closure {t : G | t ∈ N ∧ IsConj u t} = V := by
    refine le_antisymm ((closure_le _).mpr fun t ht => hinside t ht.1 ht.2) ?_
    intro v hv
    by_cases hv1 : v=1
    · simpa only [hv1] using (closure {t : G | t ∈ N ∧ IsConj u t}).one_mem
    · exact subset_closure ⟨hVN hv,hclass v hv hv1⟩
  let : Group.IsNilpotent P := hP.isNilpotent
  have hnormalizer : normalizer (N.subgroupOf P : Set P) ≤ N.subgroupOf P := by
    intro g hg
    have hgN : (g:G) ∈ normalizer (N:Set G) := by
      rw [←subgroupOf_normalizer_eq (show N≤P from inf_le_left)] at hg
      exact hg
    refine ⟨g.property,?_⟩
    rw [←hgen]
    exact normalizer_le_normalizer_conjugacy_generated N u hgN
  have hNtop : N.subgroupOf P = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent) _
      (le_antisymm hnormalizer (N.subgroupOf P).le_normalizer)
  exact fun t ht htu => hinside t (subgroupOf_eq_top.mp hNtop ht) htu

/-- A fusion-closed normal core absorbs the relevant involution class in
any overgroup containing the supplied Sylow subgroup. -/
theorem class_mem_of_normalized_core_and_sylow
    [Finite G] (T : Sylow 2 G) (R H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hHN : H ≤ normalizer (R : Set G))
    (u : T) (hu : orderOf u = 2) (huR : (u:G) ∈ R)
    (hclosed : ∀ r t : T, orderOf r=2 → (r:G)∈R → IsConj (r:G) (t:G) → (t:G)∈R)
    (t : G) (ht : t ∈ H) (hut : IsConj (u:G) t) : t ∈ R := by
  let tH : H := ⟨t,ht⟩
  have ht2 : orderOf tH = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hut
    have he : MulAut.conj g (u:G)=t := hg
    rw [←orderOf_coe tH]
    change orderOf t=2
    rw [←he,MulEquiv.orderOf_eq,orderOf_coe,hu]
  have hp : IsPGroup 2 (zpowers tH) := IsPGroup.of_card (n:=1)
    (by rw [Nat.card_zpowers,ht2,pow_one])
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P (T.subtype hTH)
  have hconjT : (g:G)*t*(g:G)⁻¹ ∈ (T:Subgroup G) := by
    have hh : (MulAut.conj g tH) ∈ ((g • P : Sylow 2 H) : Subgroup H) :=
      mem_map_of_mem (MulAut.conj g).toMonoidHom (hP (mem_zpowers tH))
    rw [hg] at hh
    exact hh
  have hc : IsConj (u:G) ((g:G)*t*(g:G)⁻¹) :=
    hut.trans (isConj_iff.mpr ⟨(g:G),rfl⟩)
  have hr := hclosed u ⟨_,hconjT⟩ hu huR hc
  exact (mem_normalizer_iff.mp (hHN g.property) t).mpr hr

/-- A two-subgroup generated by an ambient class can be compared with
that class inside any Sylow subgroup of a conjugate element centralizer. -/
theorem not_isConj_of_nonabelian_class_and_abelian_sylow_class
    [Finite G] (u s x : G) (I : Subgroup G) (hIp : IsPGroup 2 I)
    (hIs : I ≤ centralizer ({s} : Set G))
    (hI : ¬ IsMulCommutative (closure {v : G | v∈I ∧ IsConj u v}))
    (P : Sylow 2 (centralizer ({x} : Set G))) (V : Subgroup G)
    [IsMulCommutative V]
    (hclass : ∀ v ∈ (P : Subgroup (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype, IsConj u v → v∈V) : ¬IsConj s x := by
  intro hsx
  obtain ⟨a,ha⟩ := isConj_iff.mp hsx
  let f := MulAut.conj a
  let C := centralizer ({x} : Set G)
  let J := I.map f.toMonoidHom
  have hJC : J ≤ C := by
    rintro y ⟨v,hv,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hs : f s=x := ha
    simpa only [map_mul,hs,MulEquiv.coe_toMonoidHom] using congrArg f (mem_centralizer_singleton_iff.mp (hIs hv))
  obtain ⟨Q,hQ⟩ := ((hIp.map f.toMonoidHom).comap_subtype (K:=C)).exists_le_sylow
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq C Q P
  let k := MulAut.conj ((b:G)*a)
  let W := closure {v : G | v∈I ∧ IsConj u v}
  have hWV : W.map k.toMonoidHom ≤ V := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro v ⟨hv,hvu⟩
    have hvJ : f v ∈ J := mem_map_of_mem f.toMonoidHom hv
    have hvQ : (⟨f v,hJC hvJ⟩:C) ∈ Q := hQ hvJ
    have hvP : MulAut.conj b (⟨f v,hJC hvJ⟩:C) ∈ (P:Subgroup C) := by
      rw [←hb]
      exact mem_map_of_mem (MulAut.conj b).toMonoidHom hvQ
    have hkP : k v ∈ (P:Subgroup C).map C.subtype := by
      have hh := mem_map_of_mem C.subtype hvP
      change (b:G)*(a*v*a⁻¹)*(b:G)⁻¹ ∈ _ at hh
      change ((b:G)*a)*v*((b:G)*a)⁻¹ ∈ _
      simpa only [mul_inv_rev,mul_assoc] using hh
    exact hclass (k v) hkP (hvu.trans (isConj_iff.mpr ⟨(b:G)*a,rfl⟩))
  apply hI
  apply le_centralizer_iff_isMulCommutative.mp
  intro v hv w hw
  apply k.injective
  have hc : k w*k v=k v*k w := congrArg Subtype.val
    (mul_comm (⟨k w,hWV (mem_map_of_mem k.toMonoidHom hw)⟩:V)
      ⟨k v,hWV (mem_map_of_mem k.toMonoidHom hv)⟩)
  simpa only [map_mul] using hc

end Subgroup
