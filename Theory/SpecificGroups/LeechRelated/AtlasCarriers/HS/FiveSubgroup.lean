module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.GroupTheory.WordSubgroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.PGroup

/-!
# A nonabelian subgroup of order 125 in the ATLAS Higman–Sims carrier

The elements are explicit words in the published degree-100 generators.
Packed permutation tables accelerate kernel checks of word identities;
they do not change the carrier or assume its order. GAP supplied candidate
words only. All identities below are checked by Lean's kernel.

Source: GLS volume 3, Table 5.3m, the subgroup `5^(1+2)`;
ATLAS HSG1-p100B0, with provenance in the parent carrier module.
The 125 products `x^i y^j z^k` are closed under left multiplication by
the generators and their inverses. Their images on letters zero and one
distinguish all normal forms, proving the order. Discovery data and a
reproducible table encoding are retained in `FiveSubgroup/source/`.
-/

public section
namespace Sporadic.LeechRelated.HS.FiveSubgroup
set_option maxRecDepth 100000
set_option Elab.async false

private def checkFin {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i, h⟩ else true)

private theorem allFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

private def aMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def aInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3838723257997737152524899170929934947202430479706805946343499194866484018493252410823467695167791695081756400242119444822672887673306494670569625348565932927976040876586221373003419306020058828375383269105214395 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem aLeft : ∀ i, aInvMap (aMap i) = i := by
  apply allFin
  decide +kernel

private def aPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm aMap aInvMap aLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin aLeft)

private theorem aPerm_eq_generator : aPerm = generatorA := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def a : Carrier := ⟨aPerm, aPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

private def bMap (i : Fin 100) : Fin 100 :=
  ⟨(1584088533044622539624716012360915100311113938083754946662587072801676726706164344372852891441442777957300990173557581617101002762039959730741693432191260900145476108926406488416286385789713123784992907581461166 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def bInvMap (i : Fin 100) : Fin 100 :=
  ⟨(852881488533531112336995551220226122361210863663080587750664607485875722147280441807057556633165462885474069200795003754517913050689892735891088239319177696223676845175972313037682728934689958756512102884170325 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem bLeft : ∀ i, bInvMap (bMap i) = i := by
  apply allFin
  decide +kernel

private def bPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm bMap bInvMap bLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin bLeft)

private theorem bPerm_eq_generator : bPerm = generatorB := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def b : Carrier := ⟨bPerm, bPerm_eq_generator.symm ▸
  Subgroup.subset_closure (by simp)⟩

private def xMap (i : Fin 100) : Fin 100 :=
  ⟨(1090768555087766126420252950901337905594533046556013374717435253739359150779575432184102945512898984121425837550415394225939833404260689161226234356667858114576334025820716773603323419649330995580902984172052701 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def xInvMap (i : Fin 100) : Fin 100 :=
  ⟨(1467673427206191104694911982846039804983566038469894144685542322248058620739222115146027845503407056478085280411141558915966411793859743878254440777067783292845986682655966183669952027048702111838524271306785502 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem xLeft : ∀ i, xInvMap (xMap i) = i := by
  apply allFin
  decide +kernel

private def xPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm xMap xInvMap xLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin xLeft)

private def xWord : Carrier := (b ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a * b * a * b * a * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * (b ^ 3) * a⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b⁻¹

private theorem xPerm_eq_word : xPerm = (xWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A certified word in the two defining HS generators. -/
def x : Carrier := ⟨xPerm, xPerm_eq_word.symm ▸ xWord.property⟩

private def yMap (i : Fin 100) : Fin 100 :=
  ⟨(1467580442129328556012666385047371778002543697739723047208027235188267559289464040340132701426559498137591547922982126450879760347400036577645405040318323578334238946971160177135893262762206491852930871953583894 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def yInvMap (i : Fin 100) : Fin 100 :=
  ⟨(2864249903161745422835385601961163030221338316536809114889613475233637133075395612864197691982326048602930126089656165225438815051100950639682993668961613576742893367045560524352735929439730452676345581078369925 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem yLeft : ∀ i, yInvMap (yMap i) = i := by
  apply allFin
  decide +kernel

private def yPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm yMap yInvMap yLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin yLeft)

private def yWord : Carrier := b * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a * b * a * (b⁻¹ ^ 3) * a⁻¹ * (b⁻¹ ^ 2)

private theorem yPerm_eq_word : yPerm = (yWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A certified word in the two defining HS generators. -/
def y : Carrier := ⟨yPerm, yPerm_eq_word.symm ▸ yWord.property⟩

private def zMap (i : Fin 100) : Fin 100 :=
  ⟨(4044655372802648191487284196021497788878242937366232096868090600938212146324892042422168752405132307796757851678758015615489894932682905538917678074457227315950185823553453198417538328540788259274896457071397032 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def zInvMap (i : Fin 100) : Fin 100 :=
  ⟨(3113999019333133078563031151322531906912886410370848583101742260590839847876474462422289616119019109045500168218436445984904780574320030025775418421937306148340985226759025039524356652994140133138767778264192772 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem zLeft : ∀ i, zInvMap (zMap i) = i := by
  apply allFin
  decide +kernel

private def zPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm zMap zInvMap zLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin zLeft)

private def zWord : Carrier := x⁻¹ * y⁻¹ * x * y

private theorem zPerm_eq_word : zPerm = (zWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- A certified word in the two defining HS generators. -/
def z : Carrier := ⟨zPerm, zPerm_eq_word.symm ▸ zWord.property⟩

theorem z_eq_commutator : z = x⁻¹ * y⁻¹ * x * y := by
  apply Subtype.ext
  exact zPerm_eq_word

theorem xy_ne_yx : x * y ≠ y * x := by
  intro h
  have he := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 0) h
  have hn : (x * y : Equiv.Perm (Fin 100)) 0 ≠ (y * x : Equiv.Perm (Fin 100)) 0 := by
    decide +kernel
  exact hn he


/-- The subgroup generated by the two certified five-elements. -/
def subgroup : Subgroup Carrier := Subgroup.closure {x, y}

private theorem x_mem : x ∈ subgroup := Subgroup.subset_closure (by simp)
private theorem y_mem : y ∈ subgroup := Subgroup.subset_closure (by simp)
private theorem z_mem : z ∈ subgroup := by
  rw [z_eq_commutator]
  exact subgroup.mul_mem (subgroup.mul_mem
    (subgroup.mul_mem (subgroup.inv_mem x_mem) (subgroup.inv_mem y_mem)) x_mem) y_mem

private def normalForm (t : Fin 125) : Carrier :=
  x ^ (t.val % 5) * y ^ (t.val / 5 % 5) * z ^ (t.val / 25)

private theorem normalForm_mem (t : Fin 125) : normalForm t ∈ subgroup :=
  subgroup.mul_mem (subgroup.mul_mem
    (subgroup.pow_mem x_mem _) (subgroup.pow_mem y_mem _)) (subgroup.pow_mem z_mem _)

private def stepX (t : Fin 125) : Fin 125 :=
  ⟨((t.val % 5 + 1) % 5 + 5 * (t.val / 5)) % 125, Nat.mod_lt _ (by decide)⟩
private def stepY (t : Fin 125) : Fin 125 :=
  ⟨(t.val % 5 + 5 * ((t.val / 5 % 5 + 1) % 5) +
    25 * ((t.val / 25 + 5 - t.val % 5) % 5)) % 125, Nat.mod_lt _ (by decide)⟩
private def stepInvX (t : Fin 125) : Fin 125 :=
  ⟨((t.val % 5 + 4) % 5 + 5 * (t.val / 5)) % 125, Nat.mod_lt _ (by decide)⟩
private def stepInvY (t : Fin 125) : Fin 125 :=
  ⟨(t.val % 5 + 5 * ((t.val / 5 % 5 + 4) % 5) +
    25 * ((t.val / 25 + t.val % 5) % 5)) % 125, Nat.mod_lt _ (by decide)⟩

private theorem x_normalForm (t : Fin 125) : x * normalForm t = normalForm (stepX t) := by
  have h : ∀ s : Fin 125, ∀ i : Fin 100,
      (x * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepX s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem y_normalForm (t : Fin 125) : y * normalForm t = normalForm (stepY t) := by
  have h : ∀ s : Fin 125, ∀ i : Fin 100,
      (y * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepY s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem inv_x_normalForm (t : Fin 125) :
    x⁻¹ * normalForm t = normalForm (stepInvX t) := by
  have h : ∀ s : Fin 125, ∀ i : Fin 100,
      (x⁻¹ * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepInvX s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem inv_y_normalForm (t : Fin 125) :
    y⁻¹ * normalForm t = normalForm (stepInvY t) := by
  have h : ∀ s : Fin 125, ∀ i : Fin 100,
      (y⁻¹ * normalForm s : Equiv.Perm (Fin 100)) i =
        (normalForm (stepInvY s) : Equiv.Perm (Fin 100)) i := by
    apply allFin
    decide +kernel
  exact Subtype.ext (Equiv.ext (h t))

private theorem normalForm_cover {g : Carrier} (hg : g ∈ subgroup) :
    ∃ t : Fin 125, normalForm t = g := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, by simp [normalForm]⟩
  | mul_left a ha b _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases (show a = x ∨ a = y by simpa using ha) with rfl | rfl
    · exact ⟨stepX t, (x_normalForm t).symm⟩
    · exact ⟨stepY t, (y_normalForm t).symm⟩
  | inv_mul_cancel a ha b _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases (show a = x ∨ a = y by simpa using ha) with rfl | rfl
    · exact ⟨stepInvX t, (inv_x_normalForm t).symm⟩
    · exact ⟨stepInvY t, (inv_y_normalForm t).symm⟩

private theorem normalForm_injective : Function.Injective normalForm := by
  have h : ∀ s t : Fin 125,
      (normalForm s : Equiv.Perm (Fin 100)) 0 = (normalForm t : Equiv.Perm (Fin 100)) 0 →
      (normalForm s : Equiv.Perm (Fin 100)) 1 = (normalForm t : Equiv.Perm (Fin 100)) 1 →
      s = t := by
    apply allFin
    decide +kernel
  intro s t he
  exact h s t (congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 0) he)
    (congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 1) he)

/-- Exhaustive normal forms, separated by their actions on two letters, give order 125. -/
theorem card_subgroup : Nat.card subgroup = 5 ^ 3 := by
  let f : Fin 125 → subgroup := fun t => ⟨normalForm t, normalForm_mem t⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      exact normalForm_injective (congrArg Subtype.val h)
    · intro g
      obtain ⟨t, ht⟩ := normalForm_cover g.property
      exact ⟨t, Subtype.ext ht⟩
  simpa using (Nat.card_eq_of_bijective f hf).symm

/-- The concrete order-125 subgroup is a five-group. -/
theorem subgroup_isPGroup : IsPGroup 5 subgroup := IsPGroup.of_card card_subgroup

/-- The two generators fail to commute already on letter zero. -/
theorem subgroup_not_commutative : ¬ IsMulCommutative subgroup := by
  intro h
  let := h
  apply xy_ne_yx
  exact congrArg Subtype.val
    (IsMulCommutative.is_comm.comm (⟨x, x_mem⟩ : subgroup) ⟨y, y_mem⟩)

end Sporadic.LeechRelated.HS.FiveSubgroup
