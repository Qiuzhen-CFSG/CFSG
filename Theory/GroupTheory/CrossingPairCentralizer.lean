module

public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupAction.ModelConjugation
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.PPrimeCore
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Faithful actions of a commuting crossing pair

If K is normal in J = C_G(t), x normalizes a Sylow subgroup S of J,
x² belongs to S and tˣ belongs to K, then t belongs to the right conjugate
Kˣ. The supplement J = KS C_J(K) makes J normalize KKˣ. Its ambient
centralizer is normal in J and meets S in C_S(K) ∩ C_S(K)ˣ; triviality of
this intersection and O(J) = 1 make that centralizer trivial.

The resulting literal conjugation actions are faithful. If the stabilizer
of t in Aut(Kˣ) is a two-group, C_J(K) is a normal two-group and hence lies
in S, giving J = KS. All normality is relative to J. Conjugate subgroup
expressions use x⁻¹ k x; the actions use the homomorphic left convention.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 2.5.21, printed p.566. The model and fusion steps are separate.
-/

public section

open Subgroup
namespace Theory.GroupTheory.CrossingPair
variable {G : Type*} [Group G]
local notation "conjugate" => (fun (A : Subgroup G) (g : G) => Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) A)

private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  ext g
  rw [mem_map_equiv]
  constructor
  · intro hg a ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hh := congrArg e (hg b hb)
    change e b * g = g * e b
    simpa only [map_mul, e.apply_symm_apply] using hh
  · intro hg a ha
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e a) (mem_map_of_mem _ ha)

private theorem singleton_centralizer_map (t : G) (e : G ≃* G) :
    (centralizer ({t} : Set G)).map e.toMonoidHom =
      centralizer ({e t} : Set G) := by
  ext g
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa only [map_mul, e.apply_symm_apply] using congrArg e h
  · intro h
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using h

/-- The crossing mark lies in the other factor; the square of x need only
normalize K. In particular the source does not assert t ∈ K. -/
theorem mark_mem_crossing_factor (K S : Subgroup G) (t x : G)
    (hSK : S ≤ normalizer (K : Set G)) (hx2 : x ^ 2 ∈ S)
    (htx : x⁻¹ * t * x ∈ K) : t ∈ conjugate K x := by
  have hnx : x ^ 2 ∈ normalizer (K : Set G) := hSK hx2
  have h : x * t * x⁻¹ ∈ K := by
    have hh : x ^ 2 * (x⁻¹ * t * x) * (x ^ 2)⁻¹ ∈ K :=
      (hnx (x⁻¹ * t * x)).mp htx
    convert hh using 1
    group
  exact ⟨x * t * x⁻¹, h, by change x⁻¹ * (x * t * x⁻¹) * (x⁻¹)⁻¹ = t; group⟩

/-- Transport normality in the full involution centralizer, with right
conjugation on both the mark and the component. -/
theorem crossing_factor_normalized (K : Subgroup G) (t x : G)
    (hJ : centralizer ({t} : Set G) ≤ normalizer (K : Set G)) :
    centralizer ({x⁻¹ * t * x} : Set G) ≤ normalizer (conjugate K x : Set G) := by
  have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hJ
  rw [singleton_centralizer_map, map_equiv_normalizer_eq] at hh
  simpa only [MulAut.conj_apply, inv_inv] using hh

/-- S also normalizes the right-conjugate component because x normalizes S. -/
theorem sylow_normalizes_crossing (K S : Subgroup G) (x : G)
    (hSK : S ≤ normalizer (K : Set G)) (hx : x ∈ normalizer (S : Set G)) :
    S ≤ normalizer (conjugate K x : Set G) := by
  have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hSK
  rw [map_equiv_normalizer_eq] at hh
  have hs := mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem hx)
  change S.map (MulAut.conj x⁻¹).toMonoidHom = S at hs
  rwa [hs] at hh

/-- The decomposition of 2.5.18/20 already makes C_G(t) normalize the pair;
no equality C_G(t) = KS is needed at this stage. -/
theorem centralizer_normalizes_pair (K S : Subgroup G) (t x : G)
    (hSJ : S ≤ centralizer ({t} : Set G))
    (hnormal : centralizer ({t} : Set G) ≤ normalizer (K : Set G))
    (hgen : centralizer ({t} : Set G) =
      K ⊔ S ⊔ (centralizer ({t} : Set G) ⊓ centralizer (K : Set G)))
    (hx : x ∈ normalizer (S : Set G))
    (htx : x⁻¹ * t * x ∈ K)
    (hc : ⁅K, conjugate K x⁆ = ⊥) :
    centralizer ({t} : Set G) ≤ normalizer ((K ⊔ conjugate K x : Subgroup G) : Set G) := by
  have hSK := hSJ.trans hnormal
  have hSL := sylow_normalizes_crossing K S x hSK hx
  have hKL : K ≤ normalizer (conjugate K x : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hCL : centralizer (K : Set G) ≤ normalizer (conjugate K x : Set G) := by
    apply le_trans _ (crossing_factor_normalized K t x hnormal)
    intro g hg
    exact mem_centralizer_singleton_iff.mpr (hg _ htx).symm
  have hJL : centralizer ({t} : Set G) ≤ normalizer (conjugate K x : Set G) := by
    rw [hgen]
    exact sup_le (sup_le hKL hSL) (inf_le_right.trans hCL)
  exact (le_inf hnormal hJL).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The actual S-centralizer of the crossing factor is the right conjugate
of D = C_S(K). -/
theorem sylow_centralizer_crossing (K S : Subgroup G) (x : G)
    (hx : x ∈ normalizer (S : Set G)) :
    S ⊓ centralizer (conjugate K x : Set G) =
      conjugate (S ⊓ centralizer (K : Set G)) x := by
  change S ⊓ centralizer (K.map (MulAut.conj x⁻¹).toMonoidHom : Set G) =
    (S ⊓ centralizer (K : Set G)).map (MulAut.conj x⁻¹).toMonoidHom
  rw [map_inf _ _ _ (MulAut.conj x⁻¹).injective, centralizer_map_equiv]
  have hs := mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem hx)
  change S.map (MulAut.conj x⁻¹).toMonoidHom = S at hs
  rw [hs]

variable [Finite G]

private theorem normal_eq_bot_of_sylow_disjoint (P : Sylow 2 G)
    (N : Subgroup G) [N.Normal]
    (hdis : (P : Subgroup G) ⊓ N = ⊥) (hO : pPrimeCore 2 G = ⊥) : N = ⊥ := by
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal N
  have hQbot : (Q : Subgroup N) = ⊥ := by
    apply map_injective N.subtype_injective
    simpa only [Subgroup.map_bot, hdis] using hQ
  have hodd : Nat.Coprime 2 (Nat.card N) := by
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro hd
    exact (Q.ne_bot_of_dvd_card hd) hQbot
  exact pPrimeCore_eq_bot_iff.mp hO N inferInstance hodd

/-- Trivial odd core and trivial intersection with the actual Sylow kill a
normal subgroup of the involution centralizer. -/
private theorem relative_normal_eq_bot (J S C : Subgroup G)
    (P : Sylow 2 J) (hP : (P : Subgroup J).map J.subtype = S)
    (hCJ : C ≤ J) (hJC : J ≤ normalizer (C : Set G))
    (hdis : S ⊓ C = ⊥) (hO : pPrimeCore 2 J = ⊥) : C = ⊥ := by
  let N := C.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hCJ).mpr hJC
  have hi : (P : Subgroup J) ⊓ N = ⊥ := by
    apply bot_unique
    intro y hy
    apply Subtype.ext
    have hh : (y : G) ∈ S ⊓ C := ⟨hP ▸ mem_map_of_mem J.subtype hy.1, hy.2⟩
    change (y : G) = 1
    simpa only [hdis, mem_bot] using hh
  have hn : N = ⊥ := normal_eq_bot_of_sylow_disjoint P N hi hO
  have hm := congrArg (fun A : Subgroup J => A.map J.subtype) hn
  simpa only [N, map_subgroupOf_eq_of_le hCJ, Subgroup.map_bot] using hm

/-- The pair has trivial ambient centralizer. This uses O(C_G(t)) = 1,
not an assumed faithful pair action or the later equality C_G(t) = KS. -/
theorem pair_centralizer_eq_bot (K S : Subgroup G) (t x : G)
    (P : Sylow 2 (centralizer ({t} : Set G)))
    (hP : (P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype = S)
    (hSJ : S ≤ centralizer ({t} : Set G))
    (hnormal : centralizer ({t} : Set G) ≤ normalizer (K : Set G))
    (hgen : centralizer ({t} : Set G) =
      K ⊔ S ⊔ (centralizer ({t} : Set G) ⊓ centralizer (K : Set G)))
    (hx : x ∈ normalizer (S : Set G)) (hx2 : x ^ 2 ∈ S)
    (htx : x⁻¹ * t * x ∈ K)
    (hc : ⁅K, conjugate K x⁆ = ⊥)
    (hdis : (S ⊓ centralizer (K : Set G)) ⊓
      conjugate (S ⊓ centralizer (K : Set G)) x = ⊥)
    (hO : pPrimeCore 2 (centralizer ({t} : Set G)) = ⊥) :
    centralizer ((K ⊔ conjugate K x : Subgroup G) : Set G) = ⊥ := by
  have htL := mark_mem_crossing_factor K S t x (hSJ.trans hnormal) hx2 htx
  have hJM := centralizer_normalizes_pair K S t x hSJ hnormal hgen hx htx hc
  apply relative_normal_eq_bot (centralizer ({t} : Set G)) S _ P hP
  · intro c hc
    exact mem_centralizer_singleton_iff.mpr (hc t (mem_sup_right htL)).symm
  · exact hJM.trans (normalizer_le_normalizer_centralizer _)
  · apply bot_unique
    intro y hy
    have hyK : y ∈ centralizer (K : Set G) := fun k hk => hy.2 k (mem_sup_left hk)
    have hyL : y ∈ centralizer (conjugate K x : Set G) := fun l hl => hy.2 l (mem_sup_right hl)
    have hyD : y ∈ conjugate (S ⊓ centralizer (K : Set G)) x := by
      rw [← sylow_centralizer_crossing K S x hx]
      exact ⟨hy.1, hyL⟩
    have hh : y ∈ (S ⊓ centralizer (K : Set G)) ⊓
        conjugate (S ⊓ centralizer (K : Set G)) x := ⟨⟨hy.1, hyK⟩, hyD⟩
    simpa only [hdis] using hh
  · exact hO

end Theory.GroupTheory.CrossingPair

namespace Theory.GroupTheory.CrossingPair
variable {G : Type*} [Group G]

/-- The literal actions on the two normal factors, restricted to A. -/
def pairAction (A K L : Subgroup G)
    (hK : A ≤ normalizer (K : Set G)) (hL : A ≤ normalizer (L : Set G)) :
    A →* MulAut K × MulAut L :=
  (K.normalizerMonoidHom.comp (inclusion hK)).prod
    (L.normalizerMonoidHom.comp (inclusion hL))

/-- The pair action kernel is the intersection of the two ambient centralizers. -/
theorem pairAction_ker (A K L : Subgroup G)
    (hK : A ≤ normalizer (K : Set G)) (hL : A ≤ normalizer (L : Set G)) :
    (pairAction A K L hK hL).ker =
      (centralizer (K : Set G) ⊓ centralizer (L : Set G)).subgroupOf A := by
  ext a
  change (K.normalizerMonoidHom (inclusion hK a),
    L.normalizerMonoidHom (inclusion hL a)) = (1, 1) ↔ _
  rw [Prod.mk.injEq]
  change (inclusion hK a ∈ K.normalizerMonoidHom.ker ∧
    inclusion hL a ∈ L.normalizerMonoidHom.ker) ↔ _
  rw [normalizerMonoidHom_ker, normalizerMonoidHom_ker]
  rfl

private theorem centralizes_join {K L : Subgroup G} {g : G}
    (hK : g ∈ centralizer (K : Set G)) (hL : g ∈ centralizer (L : Set G)) :
    g ∈ centralizer ((K ⊔ L : Subgroup G) : Set G) := by
  have hk : K ≤ centralizer ({g} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hK k hk)
  have hl : L ≤ centralizer ({g} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.mpr (hL l hl)
  intro a ha
  exact mem_centralizer_singleton_iff.mp (sup_le hk hl ha)

/-- Trivial centralizer of the pair gives faithfulness of its actual action. -/
theorem pairAction_injective (A K L : Subgroup G)
    (hK : A ≤ normalizer (K : Set G)) (hL : A ≤ normalizer (L : Set G))
    (hC : centralizer ((K ⊔ L : Subgroup G) : Set G) = ⊥) :
    Function.Injective (pairAction A K L hK hL) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [pairAction_ker]
  apply bot_unique
  intro a ha
  apply Subtype.ext
  change (a : G) = 1
  have hh : (a : G) ∈ centralizer ((K ⊔ L : Subgroup G) : Set G) :=
    centralizes_join ha.1 ha.2
  simpa only [hC, mem_bot] using hh

/-- Restrict to C_A(K): its action on L is faithful when the pair centralizer
is trivial, and fixes the actual marked element t of L. -/
theorem centralizer_isTwoGroup_of_fixed_action
    (A K L : Subgroup G) (hL : A ≤ normalizer (L : Set G))
    (hC : centralizer ((K ⊔ L : Subgroup G) : Set G) = ⊥)
    (t : L) (hAt : A ≤ centralizer ({(t : G)} : Set G))
    (hfix : IsPGroup 2 (MulAction.stabilizer (MulAut L) t)) :
    IsPGroup 2 (A ⊓ centralizer (K : Set G) : Subgroup G) := by
  let D := A ⊓ centralizer (K : Set G)
  let rho : D →* MulAut L :=
    L.normalizerMonoidHom.comp (inclusion (inf_le_left.trans hL))
  have hfixed : ∀ d : D, rho d ∈ MulAction.stabilizer (MulAut L) t := by
    intro d
    change rho d t = t
    apply Subtype.ext
    change (d : G) * (t : G) * (d : G)⁻¹ = (t : G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hAt d.property.1))
  let f := rho.codRestrict (MulAction.stabilizer (MulAut L) t) hfixed
  apply hfix.of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro d hd
  have he : rho d = 1 := congrArg Subtype.val hd
  have hLd : (d : G) ∈ centralizer (L : Set G) := by
    change inclusion (inf_le_left.trans hL) d ∈ L.normalizerMonoidHom.ker at he
    rwa [normalizerMonoidHom_ker] at he
  apply Subtype.ext
  change (d : G) = 1
  have hh := centralizes_join d.property.2 hLd
  simpa only [hC, mem_bot] using hh

/-- A normal two-group centralizer is contained in the supplied Sylow,
so the earlier centralizer supplement collapses to KS. -/
theorem centralizer_supplement_eq (J K S : Subgroup G)
    (P : Sylow 2 J) (hP : (P : Subgroup J).map J.subtype = S)
    (hKJ : K ≤ J) (hn : J ≤ normalizer (K : Set G))
    (hgen : J = K ⊔ S ⊔ (J ⊓ centralizer (K : Set G)))
    (hC : IsPGroup 2 (J ⊓ centralizer (K : Set G) : Subgroup G)) :
    J = K ⊔ S := by
  let KJ := K.subgroupOf J
  let : KJ.Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr hn
  have hcJ : (centralizer (K : Set G)).subgroupOf J = centralizer (KJ : Set J) := by
    ext j
    constructor
    · intro hj k hk
      apply Subtype.ext
      exact hj k.val hk
    · intro hj k hk
      exact congrArg Subtype.val (hj ⟨k, hKJ hk⟩ hk)
  let C := (centralizer (K : Set G)).subgroupOf J
  let : C.Normal := by
    change ((centralizer (K : Set G)).subgroupOf J).Normal
    rw [hcJ]
    infer_instance
  have hpC : IsPGroup 2 C := by
    let e : C ≃* (J ⊓ centralizer (K : Set G) : Subgroup G) :=
      { toFun := fun c => ⟨c.val.val, c.val.property, c.property⟩
        invFun := fun c => ⟨⟨c.val, c.property.1⟩, c.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact hC.of_equiv e.symm
  have hCS : J ⊓ centralizer (K : Set G) ≤ S := by
    intro c hc
    have hh := hpC.le_sylow_of_normal P (show (⟨c, hc.1⟩ : J) ∈ C from hc.2)
    rw [← hP]
    exact mem_map_of_mem J.subtype hh
  calc
    J = K ⊔ S ⊔ (J ⊓ centralizer (K : Set G)) := hgen
    _ = K ⊔ S := sup_eq_left.mpr (hCS.trans le_sup_right)
end Theory.GroupTheory.CrossingPair

end
