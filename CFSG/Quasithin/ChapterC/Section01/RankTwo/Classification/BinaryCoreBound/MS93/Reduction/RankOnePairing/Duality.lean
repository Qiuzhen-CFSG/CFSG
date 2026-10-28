module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# The contragredient quotient in original MS93 (1.7)(ii)

The natural factor of U/C_U(W) is contragredient to the specified natural Z,
using Z's actual quotient marking. The construction returns surjective
coordinates on U with kernel C_U(W), together with the inverse-transpose
conjugation equation. The full component image and Z centralizing the extension
core remain the two explicit local-structure inputs allowed by the source
assembly; the local incidence conclusions are not used.

First descend ambient conjugation to the intrinsic coordinate quotient. The
normal two-core has a nonidentity fixed point on the quotient’s eight elements. The
component is transitive on the seven nonzero vectors, so normality makes the
whole factor fixed. Clause (A) then gives M = LQ and extends the natural action
formula to M, including the untilded local residual L_alpha.

Next C/Z = C_(U/Z)(L) maps to zero in the natural factor. Thus the seed X has a
nonzero image fixed by L_alpha. An inner difference between the two markings
would transport this vector to a nonidentity element of C_Z(L_alpha). Excluding
that case, the proved inner/graph automorphism decomposition supplies a change
of coordinates whose action is exactly inverse transpose.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation on pp.828--829,832 and (1.7)(ii), pp.847--848, specialized to
q = 2. The elementwise commutator clause of (ii) belongs to the incidence and
source-theorem assembly, not to this module's conclusion.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Duality
open Subgroup
open scoped Matrix commutatorElement

private abbrev V := Fin 3 → ZMod 2
private abbrev E := Multiplicative V

private def singer : SL := ⟨!![0,0,1;1,0,1;0,1,0], by decide⟩

private theorem singer_fixed (v : V) (h : singer.val.mulVec v = v) : v = 0 := by
  have hf : ∀ v : V, singer.val.mulVec v = v → v = 0 := by decide
  exact hf v h

private theorem natural_transitive (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL, g.val.mulVec v = w := by
  have ht : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      ∃ k : Fin 7, (singer ^ k.val).val.mulVec v = w := by decide
  obtain ⟨k, hk⟩ := ht v w hv hw
  exact ⟨singer ^ k.val, hk⟩

private theorem untwist (g a : SL) (v : V) :
    g⁻¹.val.mulVec ((g * a * g⁻¹).val.mulVec v) =
      a.val.mulVec (g⁻¹.val.mulVec v) := by
  have h : g⁻¹ * (g * a * g⁻¹) = a * g⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec] using
    congrArg (fun b : SL => b.val.mulVec v) h

universe u
variable {M : Type u} [Group M]

private noncomputable def coordinateConj (H N : Subgroup M) [H.Normal] [N.Normal]
    (f : H →* E) (hf : Function.Surjective f) (hk : f.ker = N.subgroupOf H)
    (m : M) : E →* E :=
  f.liftOfSurjective hf ⟨f.comp (MulAut.conjNormal m).toMonoidHom, by
    intro x hx
    change f (MulAut.conjNormal m x) = 1
    apply MonoidHom.mem_ker.mp
    rw [hk]
    exact (inferInstance : N.Normal).conj_mem x
      (show x ∈ N.subgroupOf H from hk ▸ hx) m⟩

private theorem coordinateConj_apply (H N : Subgroup M) [H.Normal] [N.Normal]
    (f : H →* E) (hf : Function.Surjective f) (hk : f.ker = N.subgroupOf H)
    (m : M) (x : H) :
    coordinateConj H N f hf hk m (f x) = f (MulAut.conjNormal m x) :=
  f.liftOfRightInverse_comp_apply _ _ _ x

@[instance_reducible] private noncomputable def coordinateAction (H N : Subgroup M) [H.Normal] [N.Normal]
    (f : H →* E) (hf : Function.Surjective f) (hk : f.ker = N.subgroupOf H) :
    MulAction M E where
  smul m v := coordinateConj H N f hf hk m v
  one_smul v := by
    obtain ⟨x, rfl⟩ := hf v
    change coordinateConj H N f hf hk 1 (f x) = f x
    rw [coordinateConj_apply]
    congr 1
    apply Subtype.ext
    simp
  mul_smul m n v := by
    obtain ⟨x, rfl⟩ := hf v
    change coordinateConj H N f hf hk (m * n) (f x) =
      coordinateConj H N f hf hk m (coordinateConj H N f hf hk n (f x))
    rw [coordinateConj_apply, coordinateConj_apply, coordinateConj_apply]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]

/-- The extension clause (A) turns a full component image into M = LQ. -/
private theorem component_sup_core [Finite M] (e : Extension (M := M))
    (hL : (component e.projection e.flag).map e.projection = ⊤) :
    component e.projection e.flag ⊔ extensionCore e.projection = ⊤ := by
  let L := component e.projection e.flag
  have hE : e.projection.ker ≤ L ⊔ extensionCore e.projection :=
    e.base.no_supplement L le_sup_left
  apply top_unique
  intro m hm
  have hi : e.projection m ∈ L.map e.projection := by rw [hL]; trivial
  obtain ⟨l, hl, he⟩ := hi
  have hk : l⁻¹ * m ∈ e.projection.ker := by
    simp [MonoidHom.mem_ker, he]
  have ht := (L ⊔ extensionCore e.projection).mul_mem (mem_sup_left hl) (hE hk)
  simpa using ht

/-- Normality of the numerator and denominator promotes natural coordinates to
all ambient conjugations. The normal two-core acts trivially on the eight-element
factor, by the fixed-point theorem and transitivity on nonzero vectors. -/
theorem natural_action_all [Finite M] (e : Extension (M := M))
    (hL : (component e.projection e.flag).map e.projection = ⊤)
    {H N : Subgroup M} [H.Normal] [N.Normal]
    (n : NaturalFactor e.projection (component e.projection e.flag) H N)
    (m : M) (x y : H) (hy : (y : M) = m * (x : M) * m⁻¹) :
    Multiplicative.toAdd (n.coordinates y) =
      (n.marking (e.projection m)).val.mulVec (Multiplicative.toAdd (n.coordinates x)) := by
  let : MulAction M E := coordinateAction H N n.coordinates n.surjective n.kernel
  have hconj (m : M) (x : H) :
      m • n.coordinates x = n.coordinates (MulAut.conjNormal m x) :=
    coordinateConj_apply H N n.coordinates n.surjective n.kernel m x
  have hone (m : M) : m • (1 : E) = 1 :=
    (coordinateConj H N n.coordinates n.surjective n.kernel m).map_one
  have hact (l : M) (hl : l ∈ component e.projection e.flag) (v : E) :
      Multiplicative.toAdd (l • v) =
        (n.marking (e.projection l)).val.mulVec v.toAdd := by
    obtain ⟨a, rfl⟩ := n.surjective v
    rw [hconj]
    exact n.action l hl a (MulAut.conjNormal l a) rfl
  let Q := extensionCore e.projection
  let : MulAction Q E := MulAction.compHom E Q.subtype
  have hcard : 2 ∣ Nat.card E := by rw [Nat.card_eq_fintype_card]; decide
  have hfixed : (1 : E) ∈ MulAction.fixedPoints Q E := fun q => hone q
  obtain ⟨v, hv, hnv⟩ :=
    (extensionCore_isPGroup e.projection).exists_fixed_point_of_prime_dvd_card_of_fixed_point
      E hcard hfixed
  have hQ (q : Q) (w : E) : (q : M) • w = w := by
    by_cases hw : w = 1
    · rw [hw]; exact hone q
    obtain ⟨g, hg⟩ := natural_transitive v.toAdd w.toAdd (Ne.symm hnv) hw
    have hi : n.marking.symm g ∈ (component e.projection e.flag).map e.projection := by
      rw [hL]; trivial
    obtain ⟨l, hl, he⟩ := hi
    have hlv : l • v = w := by
      apply Multiplicative.toAdd.injective
      rw [hact l hl, he, n.marking.apply_symm_apply]
      exact hg
    rw [← hlv]
    have hq : l⁻¹ * (q : M) * l ∈ Q :=
      (inferInstance : Q.Normal).conj_mem' _ q.property l
    have hfix : (l⁻¹ * (q : M) * l) • v = v := hv ⟨_, hq⟩
    calc
      (q : M) • (l • v) = l • ((l⁻¹ * (q : M) * l) • v) := by
        simp only [← mul_smul]
        congr 1
        group
      _ = l • v := congrArg (fun z : E => l • z) hfix
  have hm : m ∈ component e.projection e.flag ⊔ Q := by
    rw [component_sup_core e hL]; trivial
  obtain ⟨l, hl, q, hq, rfl⟩ := mem_sup_of_normal_right.mp hm
  have heq : y = MulAut.conjNormal (l * q) x := Subtype.ext hy
  rw [heq, ← hconj, mul_smul, hQ ⟨q, hq⟩]
  have hqπ : e.projection q = 1 := extensionCore_le_kernel e.projection hq
  simpa only [map_mul, hqπ, mul_one] using hact l hl (n.coordinates x)

private theorem coordinates_conj_eq (H N : Subgroup M) [H.Normal]
    (f : H →* E) (hk : f.ker = N.subgroupOf H) (m : M) (x : H)
    (hc : ⁅m, (x : M)⁆ ∈ N) :
    f (MulAut.conjNormal m x) = f x := by
  apply mul_inv_eq_one.mp
  rw [← map_inv, ← map_mul]
  apply MonoidHom.mem_ker.mp
  rw [hk]
  exact hc

/-- The preimage of the global fixed space is in the actual pairing radical. -/
theorem fixedPreimage_le_centralizer [Finite M]
    {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M)))
    (hL : (component e.projection e.flag).map e.projection = ⊤)
    (hZQ : Z ≤ centralizer (extensionCore e.projection : Set M)) :
    fixedPreimage (component e.projection e.flag) X Z ≤ centralizer (W : Set M) := by
  have hZW : Z ≤ centralizer (W : Set M) := hZQ.trans (centralizer_le d.w_le)
  intro c hc
  obtain ⟨hcU, hcL⟩ := (mem_fixedPreimage _ _ _ c).mp hc
  let x : generated X := ⟨c, hcU⟩
  have hv : (n.coordinates x).toAdd = 0 := by
    have hi : n.marking.symm singer ∈ (component e.projection e.flag).map e.projection := by
      rw [hL]; trivial
    obtain ⟨l, hl, he⟩ := hi
    apply singer_fixed
    have ha := n.action l hl x (MulAut.conjNormal l x) rfl
    rw [coordinates_conj_eq _ _ n.coordinates n.kernel l x (hZW (hcL l hl)),
      he, n.marking.apply_symm_apply] at ha
    exact ha.symm
  have hx : x ∈ n.coordinates.ker := congrArg Multiplicative.ofAdd hv
  rw [n.kernel] at hx
  exact hx

private noncomputable def changeCoordinates (g : SL) : E ≃* E :=
  AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' g⁻¹).toAddEquiv

private theorem changeCoordinates_apply (g : SL) (v : E) :
    (changeCoordinates g v).toAdd = g⁻¹.val.mulVec v.toAdd := rfl

private theorem relative_marking_not_inner [Finite M]
    {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M)))
    (hL : (component e.projection e.flag).map e.projection = ⊤)
    (hZQ : Z ≤ centralizer (extensionCore e.projection : Set M))
    (hfix : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥) :
    d.natural.marking.symm.trans n.marking ∉ MulAut.innerSubgroup SL := by
  rintro ⟨g, hg⟩
  have hm (a : M) : n.marking (e.projection a) =
      g * d.natural.marking (e.projection a) * g⁻¹ := by
    have he := congrArg (fun f : MulAut SL => f (d.natural.marking (e.projection a))) hg
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] using he.symm
  have hX : ¬ X ≤ centralizer (W : Set M) := by
    intro hx
    have hb := commutator_eq_bot_iff_le_centralizer.mpr hx
    exact d.commutator_nontrivial (by rw [hb]; exact card_bot)
  obtain ⟨a, ha, haw⟩ := Set.not_subset.mp hX
  let x : generated X := ⟨a, le_normalClosure ha⟩
  have hx : n.coordinates x ≠ 1 := by
    intro hn
    exact haw (show x ∈ (centralizer (W : Set M)).subgroupOf (generated X) from
      n.kernel ▸ (show x ∈ n.coordinates.ker from hn))
  let t := changeCoordinates g
  let z : Z := d.natural.equivOfBot.symm (t (n.coordinates x))
  have hz : d.natural.coordinates z = t (n.coordinates x) :=
    d.natural.equivOfBot.apply_symm_apply _
  have hzne : (z : M) ≠ 1 := by
    intro h
    have hz1 : z = 1 := Subtype.ext h
    have ht : t (n.coordinates x) = t 1 := by rw [← hz, hz1, map_one, map_one]
    exact hx (t.injective ht)
  have hc := fixedPreimage_le_centralizer d n hL hZQ
  have hzc : (z : M) ∈ centralizer (localResidual (localParabolic e i) : Set M) := by
    apply mem_centralizer_iff.mpr
    intro b hb
    have hcomm : ⁅b, (x : M)⁆ ∈ centralizer (W : Set M) := by
      apply hc
      apply d.seed_fixed
      rw [commutator_comm]
      exact commutator_mem_commutator hb ha
    have hcx := coordinates_conj_eq _ _ n.coordinates n.kernel b x hcomm
    have hu := natural_action_all e hL n b x (MulAut.conjNormal b x) rfl
    rw [hcx] at hu
    have hv : (d.natural.marking (e.projection b)).val.mulVec
        (t (n.coordinates x)).toAdd = (t (n.coordinates x)).toAdd := by
      have hh := congrArg (fun v : V => g⁻¹.val.mulVec v) hu.symm
      rw [hm, untwist] at hh
      change (d.natural.marking (e.projection b)).val.mulVec
        (changeCoordinates g (n.coordinates x)).toAdd =
        (changeCoordinates g (n.coordinates x)).toAdd
      rw [changeCoordinates_apply]
      exact hh
    have hzconj := natural_action_all e hL d.natural b z (MulAut.conjNormal b z) rfl
    rw [hz, hv] at hzconj
    have he : MulAut.conjNormal b z = z := by
      apply d.natural.equivOfBot.injective
      exact Multiplicative.toAdd.injective (hzconj.trans (congrArg Multiplicative.toAdd hz.symm))
    have he' : b * (z : M) * b⁻¹ = (z : M) := congrArg Subtype.val he
    exact mul_inv_eq_iff_eq_mul.mp he'
  exact hzne (mem_bot.mp (show (z : M) ∈ (⊥ : Subgroup M) from hfix ▸ ⟨z.property, hzc⟩))

/-- Original MS93 (1.7)(ii), the contragredient conclusion: the coordinate map
has precisely C_U(W) as kernel and uses inverse transpose for Z's own marking.
The full component image and centralization of the extension core are explicit
local-structure inputs to be discharged by the source assembly. -/
noncomputable def contragredient [Finite M]
    {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M)))
    (hL : (component e.projection e.flag).map e.projection = ⊤)
    (hZQ : Z ≤ centralizer (extensionCore e.projection : Set M))
    (hfix : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥) :
    DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural := by
  let r := d.natural.marking.symm.trans n.marking
  have hr := relative_marking_not_inner d n hL hZQ hfix
  let outer := BinaryLinearThree.AutomorphismAction.outer_eq_inner_graph r hr
  let g := Classical.choose outer
  have hg := Classical.choose_spec outer
  let t := changeCoordinates g
  refine
    { coordinates := t.toMonoidHom.comp n.coordinates
      surjective := t.surjective.comp n.surjective
      kernel := ?_
      normalized := n.normalized
      action := ?_ }
  · ext x
    change t (n.coordinates x) = 1 ↔ x ∈ (centralizer (W : Set M)).subgroupOf (generated X)
    rw [← t.map_one, t.injective.eq_iff]
    exact SetLike.ext_iff.mp n.kernel x
  · intro l hl x y hy
    change (changeCoordinates g (n.coordinates y)).toAdd =
      ((d.natural.marking (e.projection l))⁻¹.val).transpose.mulVec
        (changeCoordinates g (n.coordinates x)).toAdd
    simp only [changeCoordinates_apply]
    rw [n.action l hl x y hy]
    have he := congrArg (fun a : MulAut SL => a (d.natural.marking (e.projection l))) hg
    have hm : n.marking (e.projection l) = g *
        BinaryLinearThree.AutomorphismAction.graph (d.natural.marking (e.projection l)) * g⁻¹ := by
      simpa only [r, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.mul_apply, MulAut.conj_apply] using he
    rw [hm, untwist]
    rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Duality
