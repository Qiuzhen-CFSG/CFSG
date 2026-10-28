module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Layers
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.LocalNormalizerUniqueness
/-!
# Generation and the central-kernel reduction for G.2.5

The three marked starred groups still need to be identified with the
point-parabolic radicals. Once their images generate L*, the two-core of
LT normalizes all three original generators. The resulting normalizing
supplement and L = O²(L) prove I = LU, without replacing g or h.

Relative normality then identifies O₂(I) with I ∩ O₂(LT). This gives the
literal quotient comparison with SL₃(F), including its compatibility with
the original star projection and conjugation on the natural module.
It also supplies the missing L≤I input to the central first layer and the
pair-intersection product proved in `Layers`.

Finally P = ⟨W,Wᵍ,Wʰ⟩ is the ordered set product WWᵍWʰ, is normal in I,
and satisfies U∩P = W and [S,I]≤P. Thus S/P is central in I/P. This module
does not assert P=S: identifying U* and eliminating that remaining central
two-group are separate source obligations, retained by structural assembly.
The exact earlier G.2.2 outputs remain explicit, as permitted by the source
branch contract; their producer is the central-closure branch of §G.2.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(1–3), printed pp.335–336, using the argument of G.2.3 on pp.333–334.
-/

@[expose] public section
open Subgroup Matrix
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

omit [Finite G] in
private theorem normalizes_conjugate {K A : Subgroup G} (x : G)
    (hx : x ∈ normalizer (K : Set G)) (hKA : K ≤ normalizer (A : Set G)) :
    K ≤ normalizer (conjugate A x : Set G) := by
  have he : K.map (MulAut.conj x⁻¹).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (K : Set G)).inv_mem hx)
  have hm := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hKA).trans
    (A.le_normalizer_map (MulAut.conj x⁻¹).toMonoidHom)
  rwa [he] at hm

/-- The join of the three marked core intersections. Its identification
with S is a central-extension obligation, not part of this definition. -/
def WProduct (D : Setup G) (g h : G) : Subgroup G :=
  (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h

namespace Hypothesis
include d

theorem T_normalizes_U : D.T ≤ normalizer (D.U : Set G) :=
  (le_sup_right.trans d.setup.local_le).trans (le_normalizer_conjugateSpanBy _ _)

theorem I_le_LU : I D g h ≤ D.L ⊔ D.U := by
  have hc (x : G) (hx : x ∈ D.L) : conjugate D.U x ≤ D.L ⊔ D.U := by
    rintro _ ⟨u, hu, rfl⟩
    change x⁻¹ * u * x⁻¹⁻¹ ∈ D.L ⊔ D.U
    rw [inv_inv]
    exact (D.L ⊔ D.U).mul_mem
      ((D.L ⊔ D.U).mul_mem ((D.L ⊔ D.U).inv_mem (mem_sup_left hx))
        (mem_sup_right hu)) (mem_sup_left hx)
  exact sup_le (sup_le le_sup_right (hc g d.g_mem)) (hc h d.h_mem)

theorem I_le_LT (hUT : D.U ≤ D.T) : I D g h ≤ D.LT :=
  (d.I_le_LU).trans (sup_le le_sup_left (hUT.trans le_sup_right))

theorem LT_core_le_T : D.LT.pCoreIn 2 ≤ D.T := by
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  rw [← hP]
  exact pCoreIn_le_sylow _ _

omit d [Field F] [Finite F] [Finite G] in
theorem LT_normalizes_core : D.LT ≤ normalizer (D.LT.pCoreIn 2 : Set G) :=
  D.LT.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)

theorem LT_core_normalizes_I : D.LT.pCoreIn 2 ≤ normalizer (I D g h : Set G) := by
  have hKU := d.LT_core_le_T.trans d.T_normalizes_U
  have hg := normalizes_conjugate g (LT_normalizes_core (mem_sup_left d.g_mem)) hKU
  have hh := normalizes_conjugate h (LT_normalizes_core (mem_sup_left d.h_mem)) hKU
  exact (le_inf ((le_inf hKU hg).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)) hh).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit d [Field F] [Finite F] [Finite G] in
theorem LU_le_I_sup_core (hstar : D.star D.L ≤ D.star (I D g h)) :
    D.L ⊔ D.U ≤ I D g h ⊔ D.LT.pCoreIn 2 := by
  apply sup_le _ ((show D.U ≤ I D g h from le_sup_left.trans le_sup_left).trans le_sup_left)
  intro l hl
  have hs : QuotientGroup.mk' (pCore 2 D.LT) ⟨l, mem_sup_left hl⟩ ∈ D.star D.L :=
    ⟨⟨l, mem_sup_left hl⟩, hl, rfl⟩
  obtain ⟨i, hi, he⟩ := hstar hs
  have hk : (⟨l, mem_sup_left hl⟩ : D.LT) * i⁻¹ ∈ pCore 2 D.LT := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 D.LT) _ = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have helem : l * (i : G)⁻¹ ∈ D.LT.pCoreIn 2 := ⟨_, hk, rfl⟩
  have hm := (I D g h ⊔ D.LT.pCoreIn 2).mul_mem (mem_sup_right helem) (mem_sup_left hi)
  simpa only [coe_subtype, inv_mul_cancel_right] using hm

/-- Starred generation lifts through the normalizing two-core supplement:
the two-residual hypothesis kills the quotient of L by its intersection with I. -/
theorem L_le_I_of_star (hstar : D.star D.L ≤ D.star (I D g h)) : D.L ≤ I D g h := by
  let J := D.L ⊔ D.U
  let K := D.LT.pCoreIn 2
  have hIJ : I D g h ≤ J := d.I_le_LU
  have hJN : J ≤ normalizer (I D g h : Set G) :=
    (LU_le_I_sup_core hstar).trans
      (sup_le (I D g h).le_normalizer d.LT_core_normalizes_I)
  let N := (I D g h).subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIJ).mpr hJN
  let q := QuotientGroup.mk' N
  have hcover : N ⊔ K.subgroupOf J = ⊤ := by
    apply top_unique
    intro x _
    have hx := (LU_le_I_sup_core hstar) x.property
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ d.LT_core_normalizes_I] at hx
    obtain ⟨i, hi, k, hk, he⟩ := hx
    change i * k = (x : G) at he
    have hkJ : k ∈ J := by
      have hxJ : i * k ∈ J := by rw [he]; exact x.property
      simpa only [inv_mul_cancel_left] using J.mul_mem (J.inv_mem (hIJ hi)) hxJ
    have hh := (N ⊔ K.subgroupOf J).mul_mem (mem_sup_left (show (⟨i, hIJ hi⟩ : J) ∈ N from hi))
      (mem_sup_right (show (⟨k, hkJ⟩ : J) ∈ K.subgroupOf J from hk))
    exact (show (⟨i, hIJ hi⟩ : J) * ⟨k, hkJ⟩ = x from Subtype.ext he) ▸ hh
  have hp : IsPGroup 2 (J ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (K.subgroupOf J)
      (isPGroup_pCoreIn 2 D.LT).comap_subtype hcover
  let f := q.comp (inclusion (show D.L ≤ J from le_sup_left))
  have hpker : IsPGroup 2 (D.L ⧸ f.ker) :=
    (hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hker : f.ker = ⊤ :=
    (pResidual_eq_top_iff 2 D.L).mp d.setup.residual f.ker inferInstance hpker
  intro l hl
  exact (QuotientGroup.eq_one_iff (N := N) (⟨l, mem_sup_left hl⟩ : J)).mp
    (MonoidHom.mem_ker.mp (show (⟨l, hl⟩ : D.L) ∈ f.ker by rw [hker]; trivial))

theorem I_eq_LU_of_star (hstar : D.star D.L ≤ D.star (I D g h)) : I D g h = D.L ⊔ D.U :=
  le_antisymm d.I_le_LU (sup_le (d.L_le_I_of_star hstar)
    (le_sup_left.trans le_sup_left))

theorem I_product_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    (I D g h : Set G) = (D.L : Set G) * (D.U : Set G) := by
  rw [d.I_eq_LU_of_star hstar]
  exact coe_mul_of_right_le_normalizer_left _ _ (hUT.trans d.setup.T_normalizes_L)

theorem LT_normalizes_I_of_star (hstar : D.star D.L ≤ D.star (I D g h)) :
    D.LT ≤ normalizer (I D g h : Set G) := by
  apply sup_le ((d.L_le_I_of_star hstar).trans (I D g h).le_normalizer)
  rw [d.I_eq_LU_of_star hstar]
  exact (le_inf d.setup.T_normalizes_L d.T_normalizes_U).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem S_le_LT_core_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) : S D g h ≤ D.LT.pCoreIn 2 :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (I D g h))
    ((pCoreIn_le 2 (I D g h)).trans (d.I_le_LT hUT))
    ((d.LT_normalizes_I_of_star hstar).trans
      (normalizer_le_normalizer_characteristic_image _ _))

theorem S_normalizes_U_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    S D g h ≤ normalizer (D.U : Set G) :=
  (d.S_le_LT_core_of_star hUT hstar).trans (d.LT_core_le_T.trans d.T_normalizes_U)

theorem S_normalizes_marked_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) (x : G) (hx : x ∈ D.L) :
    S D g h ≤ normalizer (conjugate D.U x : Set G) :=
  normalizes_conjugate x
    (I_normalizes_core D g h (d.L_le_I_of_star hstar hx))
    (d.S_normalizes_U_of_star hUT hstar)

/-- The kernel comparison is a conclusion of relative normality in LT,
not an assumption identifying the two different two-cores. -/
theorem S_eq_star_kernel_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    S D g h = I D g h ⊓ D.LT.pCoreIn 2 := by
  apply le_antisymm (le_inf (pCoreIn_le 2 _) (d.S_le_LT_core_of_star hUT hstar))
  apply le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 D.LT).of_injective (inclusion inf_le_right) (inclusion_injective _))
    inf_le_left
  exact (le_inf (I D g h).le_normalizer ((d.I_le_LT hUT).trans LT_normalizes_core)).trans
    inf_normalizer_le_normalizer_inf

/-- The restriction of the original star map, with target the original L*.
The equality of starred images is the remaining matrix-generation input. -/
def IStarProjection (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) : I D g h →* D.star D.L :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion (d.I_le_LT hUT))).codRestrict _
    (fun i => hstar ▸ (show QuotientGroup.mk' (pCore 2 D.LT)
      (inclusion (d.I_le_LT hUT) i) ∈ D.star (I D g h) from
        ⟨inclusion (d.I_le_LT hUT) i, i.property, rfl⟩))

theorem IStarProjection_surjective (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    Function.Surjective (d.IStarProjection hUT hstar) := by
  intro q
  have hq : (q : D.Star) ∈ D.star (I D g h) := by rw [hstar]; exact q.property
  obtain ⟨i, hi, he⟩ := hq
  exact ⟨⟨i, hi⟩, Subtype.ext he⟩

theorem IStarProjection_ker (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    (d.IStarProjection hUT hstar).ker = pCore 2 (I D g h) := by
  ext i
  have hs := d.S_eq_star_kernel_of_star hUT hstar.ge
  have hiff : i ∈ (d.IStarProjection hUT hstar).ker ↔ (i : G) ∈ D.LT.pCoreIn 2 := by
    change (d.IStarProjection hUT hstar) i = 1 ↔ _
    rw [Subtype.ext_iff]
    change QuotientGroup.mk' (pCore 2 D.LT) (inclusion (d.I_le_LT hUT) i) = 1 ↔ _
    change (QuotientGroup.mk (inclusion (d.I_le_LT hUT) i) : D.Star) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hi
      exact ⟨_, hi, rfl⟩
    · rintro ⟨j, hj, he⟩
      exact (show j = inclusion (d.I_le_LT hUT) i from Subtype.ext he) ▸ hj
  rw [hiff]
  constructor
  · intro hi
    have hiS : (i : G) ∈ S D g h := hs.symm ▸ ⟨i.property, hi⟩
    obtain ⟨j, hj, he⟩ := hiS
    exact (show j = i from Subtype.ext he) ▸ hj
  · intro hi
    have hiS : (i : G) ∈ S D g h := ⟨i, hi, rfl⟩
    exact (hs ▸ hiS).2

/-- The quotient comparison is induced by the source's actual star map. -/
noncomputable def coreQuotientEquiv (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) :
    (I D g h ⧸ pCore 2 (I D g h)) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
  ((QuotientGroup.quotientMulEquivOfEq (d.IStarProjection_ker hUT hstar).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (d.IStarProjection hUT hstar)
      (d.IStarProjection_surjective hUT hstar))).trans d.model

theorem coreQuotientEquiv_mk (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) (i : I D g h) :
    d.coreQuotientEquiv hUT hstar (QuotientGroup.mk' (pCore 2 (I D g h)) i) =
      d.model (d.IStarProjection hUT hstar i) := rfl

theorem coreQuotientEquiv_on_L (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) (l : D.L) :
    d.coreQuotientEquiv hUT hstar (QuotientGroup.mk' (pCore 2 (I D g h))
      (inclusion (d.L_le_I_of_star hstar.ge) l)) = d.model (starProjection D l) := rfl

theorem central_first_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    D.V ≤ S D g h ⊓ centralizer (S D g h : Set G) :=
  d.central_first hUT (d.L_le_I_of_star hstar)

theorem S₃_product_of_star (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    (S₃ D g h : Set G) =
      ((W D g h ⊓ conjugate (W D g h) g : Subgroup G) : Set G) *
        ((W D g h ⊓ conjugate (W D g h) h : Subgroup G) : Set G) *
        ((conjugate (W D g h) g ⊓ conjugate (W D g h) h : Subgroup G) : Set G) :=
  d.S₃_product hUT hf (d.L_le_I_of_star hstar)


theorem LT_core_centralizes_V : D.LT.pCoreIn 2 ≤ centralizer (D.V : Set G) := by
  let := d.setup.elementary
  exact pCoreIn_le_centralizer_of_irreducible D.V D.L D.LT
    (IsElementaryAbelian.isPGroup 2 D.V) (d.setup.V_le_T.trans le_sup_right)
    (sup_le (normalizes_of_span D d.span_eq) d.setup.T_normalizes_V) le_sup_left d.irreducible

/-- The comparison also preserves conjugation on the actual natural module,
for every element of I, rather than only for the original subgroup L. -/
theorem IStarProjection_equivariant (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) (i : I D g h) (v : D.V) :
    (d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩).toAdd =
      (d.model (d.IStarProjection hUT hstar i)).val *ᵥ (d.coordinates v).toAdd := by
  obtain ⟨l, hl⟩ := starProjection_surjective D (d.IStarProjection hUT hstar i)
  have he : QuotientGroup.mk' (pCore 2 D.LT) (inclusion (d.I_le_LT hUT) i) =
      QuotientGroup.mk' (pCore 2 D.LT) (inclusion (show D.L ≤ D.LT from le_sup_left) l) :=
    (congrArg Subtype.val hl).symm
  let k : D.LT := inclusion (d.I_le_LT hUT) i *
    (inclusion (show D.L ≤ D.LT from le_sup_left) l)⁻¹
  have hk : k ∈ pCore 2 D.LT := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pCore 2 D.LT) k = 1
    simp only [k, map_mul, map_inv, he, mul_inv_cancel]
  have hkc := d.LT_core_centralizes_V (show (k : G) ∈ D.LT.pCoreIn 2 from ⟨k, hk, rfl⟩)
  have hvl : (l : G) * v * (l : G)⁻¹ ∈ D.V :=
    (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq l.property) v).mp v.property
  have hc := hkc _ hvl
  have hc' : (k : G) * ((l : G) * v * (l : G)⁻¹) * (k : G)⁻¹ =
      (l : G) * v * (l : G)⁻¹ := by
    rw [← hc, mul_inv_cancel_right]
  have hconj : (i : G) * v * (i : G)⁻¹ = (l : G) * v * (l : G)⁻¹ := by
    calc
      _ = (k : G) * ((l : G) * v * (l : G)⁻¹) * (k : G)⁻¹ := by
        change _ = ((i : G) * (l : G)⁻¹) * ((l : G) * v * (l : G)⁻¹) *
          ((i : G) * (l : G)⁻¹)⁻¹
        group
      _ = _ := hc'
  have heq : (⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩ : D.V) =
      ⟨(l : G) * v * (l : G)⁻¹, hvl⟩ := Subtype.ext hconj
  rw [heq, ← hl]
  exact d.equivariant l v

/-- Natural conjugation through I/O₂(I), with the same quotient map used
by `coreQuotientEquiv`. -/
theorem coreQuotientEquiv_equivariant (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L) (i : I D g h) (v : D.V) :
    (d.coordinates ⟨(i : G) * v * (i : G)⁻¹,
      (mem_normalizer_iff.mp (d.I_normalizes hUT i.property) v).mp v.property⟩).toAdd =
      (d.coreQuotientEquiv hUT hstar (QuotientGroup.mk' (pCore 2 (I D g h)) i)).val *ᵥ
        (d.coordinates v).toAdd :=
  d.IStarProjection_equivariant hUT hstar i v


theorem WProduct_le_S (hstar : D.star D.L ≤ D.star (I D g h)) : WProduct D g h ≤ S D g h := by
  have hLI := d.L_le_I_of_star hstar
  change (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h ≤ _
  rw [conjugate_W D g h g (hLI d.g_mem), conjugate_W D g h h (hLI d.h_mem)]
  exact sup_le (sup_le inf_le_right inf_le_right) inf_le_right

theorem S_normalizes_W_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    S D g h ≤ normalizer (W D g h : Set G) :=
  (le_inf (d.S_normalizes_U_of_star hUT hstar) (S D g h).le_normalizer).trans
    inf_normalizer_le_normalizer_inf

theorem S_normalizes_marked_W_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) (x : G) (hx : x ∈ D.L) :
    S D g h ≤ normalizer (conjugate (W D g h) x : Set G) :=
  normalizes_conjugate x
    (I_normalizes_core D g h (d.L_le_I_of_star hstar hx))
    (d.S_normalizes_W_of_star hUT hstar)

/-- The join P is the literal ordered product WWᵍWʰ. This step does not
assert that the residual central kernel S/P vanishes. -/
theorem WProduct_eq_product (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    (WProduct D g h : Set G) =
      (W D g h : Set G) * (conjugate (W D g h) g : Set G) *
        (conjugate (W D g h) h : Set G) := by
  have hWS : W D g h ≤ S D g h := inf_le_right
  have hWgS : conjugate (W D g h) g ≤ S D g h := by
    rw [conjugate_W D g h g (d.L_le_I_of_star hstar d.g_mem)]
    exact inf_le_right
  change (((W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h : Subgroup G) : Set G) = _
  rw [coe_mul_of_left_le_normalizer_right _ _
      ((sup_le hWS hWgS).trans (d.S_normalizes_marked_W_of_star hUT hstar h d.h_mem)),
    coe_mul_of_left_le_normalizer_right _ _
      (hWS.trans (d.S_normalizes_marked_W_of_star hUT hstar g d.g_mem))]

/-- Every generator of I centralizes S modulo the actual product P. -/
theorem commutator_S_I_le_WProduct (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    ⁅S D g h, I D g h⁆ ≤ WProduct D g h := by
  have hLI := d.L_le_I_of_star hstar
  have hUI : D.U ≤ I D g h := le_sup_left.trans le_sup_left
  have hUgI : conjugate D.U g ≤ I D g h := le_sup_right.trans le_sup_left
  have hUhI : conjugate D.U h ≤ I D g h := le_sup_right
  have hbound (A : Subgroup G) (hAI : A ≤ I D g h)
      (hSA : S D g h ≤ normalizer (A : Set G)) : ⁅A, S D g h⁆ ≤ A ⊓ S D g h :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hSA)
      (le_normalizer_iff_commutator_le_right.mp (hAI.trans (I_normalizes_core D g h)))
  have hU : ⁅D.U, S D g h⁆ ≤ WProduct D g h :=
    (hbound _ hUI (d.S_normalizes_U_of_star hUT hstar)).trans (le_sup_left.trans le_sup_left)
  have hUg : ⁅conjugate D.U g, S D g h⁆ ≤ WProduct D g h := by
    have hh := hbound _ hUgI (d.S_normalizes_marked_of_star hUT hstar g d.g_mem)
    rw [← conjugate_W D g h g (hLI d.g_mem)] at hh
    exact hh.trans (le_sup_right.trans le_sup_left)
  have hUh : ⁅conjugate D.U h, S D g h⁆ ≤ WProduct D g h := by
    have hh := hbound _ hUhI (d.S_normalizes_marked_of_star hUT hstar h d.h_mem)
    rw [← conjugate_W D g h h (hLI d.h_mem)] at hh
    exact hh.trans le_sup_right
  have hgen : I D g h ≤ commutatorPreimage (I D g h) (S D g h) (WProduct D g h) :=
    sup_le (sup_le (le_commutatorPreimage hUI hU) (le_commutatorPreimage hUgI hUg))
      (le_commutatorPreimage hUhI hUh)
  have hPS := d.WProduct_le_S hstar
  have hIP : I D g h ≤ normalizer (WProduct D g h : Set G) := by
    apply sup_le (sup_le ?_ ?_) ?_
    · exact le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hPS).trans hU)
    · exact le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hPS).trans hUg)
    · exact le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl hPS).trans hUh)
  rw [commutator_comm]
  exact (commutator_mono hgen le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hIP)


/-- P is normal in the original I, as required to form the central extension. -/
theorem WProduct_normal (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h)) :
    ((WProduct D g h).subgroupOf (I D g h)).Normal := by
  have hPS := d.WProduct_le_S hstar
  apply (normal_subgroupOf_iff_le_normalizer (hPS.trans (pCoreIn_le 2 _))).mpr
  exact le_normalizer_iff_commutator_le_left.mpr
    ((commutator_mono hPS le_rfl).trans (d.commutator_S_I_le_WProduct hUT hstar))

/-- The exact kernel on U when passing to I/P is W. -/
theorem U_inf_WProduct (hstar : D.star D.L ≤ D.star (I D g h)) :
    D.U ⊓ WProduct D g h = W D g h :=
  le_antisymm (inf_le_inf_left _ (d.WProduct_le_S hstar))
    (le_inf inf_le_left (le_sup_left.trans le_sup_left))

/-- The remaining obstruction is precisely the central two-group S/P
in the literal quotient of I. No vanishing assertion is assumed here. -/
theorem image_S_le_center_productQuotient (hUT : D.U ≤ D.T)
    (hstar : D.star D.L ≤ D.star (I D g h))
    [((WProduct D g h).subgroupOf (I D g h)).Normal] :
    ((S D g h).subgroupOf (I D g h)).map
      (QuotientGroup.mk' ((WProduct D g h).subgroupOf (I D g h))) ≤
        center (I D g h ⧸ (WProduct D g h).subgroupOf (I D g h)) := by
  let q := QuotientGroup.mk' ((WProduct D g h).subgroupOf (I D g h))
  have hc : ⁅(S D g h).subgroupOf (I D g h), (⊤ : Subgroup (I D g h))⁆ ≤
      (WProduct D g h).subgroupOf (I D g h) := by
    intro x hx
    have hm := mem_map_of_mem (I D g h).subtype hx
    rw [map_commutator, map_subgroupOf_eq_of_le (show S D g h ≤ I D g h from pCoreIn_le 2 _),
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact d.commutator_S_I_le_WProduct hUT hstar hm
  apply commutator_top_right_eq_bot_iff_le_center.mp
  rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective _), ← map_commutator]
  exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hc)

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
