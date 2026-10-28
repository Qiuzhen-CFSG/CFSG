module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.Reduction
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ComponentRestriction

/-!
# Eliminating the swapped component enlargement

This is the swapped branch of the proof of 16.3.5, conditional on the literal
solvable-residual equality supplied by 16.1.7(2). For commuting quasisimple
factors `J` and `J.conjBy t`, the map `x ↦ x * t*x*t⁻¹` is a homomorphism
with perfect image in the involution centralizer. Its image therefore lies
in the given residual `L`. This ambient calculation works for central products.

The order-four group permutes the two components and has a nonidentity factor
stabilizer. Since a group of order four is abelian, this stabilizer commutes
with `t`. Fixing the diagonal image forces its commutators with `J` into the
other, commuting factor; perfectness of `J` then forces it to centralize both
factors. Restricting the components `L` and `J` to that product gives the final
contradiction. Elementary abelianness and faithfulness on the product are not
premises of this argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of 16.3.5,
printed pp.1178–1179 / PDF pp.1195–1196; residual clause in 16.1.7(2),
printed pp.1172–1173 / PDF pp.1189–1190.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.Swapped
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G]

private theorem conjBy_mul (J : Subgroup G) (a b : G) :
    J.conjBy (a * b) = (J.conjBy b).conjBy a := by
  unfold Subgroup.conjBy
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem component_eq_factor {J K M H : Subgroup G}
    (hJ : ComponentTransfer.IsComponentIn J H)
    (hK : ComponentTransfer.IsComponentIn K H)
    (hM : ComponentTransfer.IsComponentIn M H) (hle : M ≤ J ⊔ K) :
    M = J ∨ M = K := by
  by_contra! hne
  have hJM : J ≤ centralizer (M : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (hM.commute_of_ne hJ hne.1))
  have hKM : K ≤ centralizer (M : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (hM.commute_of_ne hK hne.2))
  have hzero := commutator_eq_bot_iff_le_centralizer.mpr (hle.trans (sup_le hJM hKM))
  let _ : IsQuasisimple M := hM.quasisimple
  rw [commutator_eq_self] at hzero
  exact (show Theory.GroupTheory.IsComponentIn M H from hM).ne_bot hzero

private theorem exists_nontrivial_normalizer [Finite G]
    {E J H I : Subgroup G} {t : G}
    (hcard : Nat.card E = 4) (htE : t ∈ E) (hEH : E ≤ H)
    (hJ : ComponentTransfer.IsComponentIn J H)
    (hI : I = J ⊔ J.conjBy t) (hn : E ≤ normalizer I) :
    ∃ e : G, e ∈ E ∧ e ≠ 1 ∧ e ∈ normalizer J := by
  obtain ⟨a, ha1, hat⟩ := ENat.exists_ne_ne_of_three_le
    (α := E) (by rw [ENat.card_eq_coe_natCard, hcard]; norm_num) 1 ⟨t, htE⟩
  have hJa : J.conjBy (a : G) ≤ I := by
    have hm := map_mono (f := (MulAut.conj (a : G)).toMonoidHom)
      (show J ≤ I from hI.symm ▸ le_sup_left)
    exact hm.trans (mem_normalizer_iff_map_conj_eq.mp (hn a.property)).le
  rcases component_eq_factor hJ (hJ.conjugate (hEH htE))
      (hJ.conjugate (hEH a.property)) (hJa.trans hI.le) with hfix | hswap
  · exact ⟨a, a.property, fun he => ha1 (Subtype.ext he),
      mem_normalizer_iff_map_conj_eq.mpr hfix⟩
  · refine ⟨t⁻¹ * a, E.mul_mem (E.inv_mem htE) a.property, ?_, ?_⟩
    · intro he
      exact hat (Subtype.ext (inv_mul_eq_one.mp he).symm)
    · apply mem_normalizer_iff_map_conj_eq.mpr
      change J.conjBy (t⁻¹ * (a : G)) = J
      rw [conjBy_mul, hswap, ← conjBy_mul]
      rw [inv_mul_cancel]
      ext x
      simp [Subgroup.conjBy, mem_map]

private def diagonalHom (J : Subgroup G) (t : G)
    (hc : ⁅J, J.conjBy t⁆ = ⊥) : J →* G where
  toFun x := (x : G) * MulAut.conj t x
  map_one' := by simp
  map_mul' x y := by
    have hxy : Commute (MulAut.conj t (x : G)) (y : G) :=
      (mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hc y.property)
        _ (mem_map_of_mem (MulAut.conj t).toMonoidHom x.property))
    simpa only [Subgroup.coe_mul, map_mul] using (hxy.mul_mul_mul_comm (x : G)
      (MulAut.conj t (y : G))).symm

private theorem diagonal_mem_residual {J I : Subgroup G} {t : G}
    [IsQuasisimple J] (hI : I = J ⊔ J.conjBy t)
    (ht : t ^ 2 = 1) (hc : ⁅J, J.conjBy t⁆ = ⊥) (x : J) :
    (x : G) * MulAut.conj t x ∈ ComponentTransfer.centralizerResidual I t := by
  let d := diagonalHom J t hc
  let _ : Group.IsPerfect d.range := Group.IsPerfect.range d
  have hfix (y : J) : MulAut.conj t (d y) = d y := by
    have htwice : MulAut.conj t (MulAut.conj t (y : G)) = y := by
      change t * (t * (y : G) * t⁻¹) * t⁻¹ = y
      have ht' : t * t = 1 := by simpa [pow_two] using ht
      calc
        _ = (t * t) * (y : G) * (t * t)⁻¹ := by group
        _ = y := by rw [ht']; simp
    have hcomm : MulAut.conj t (y : G) * (y : G) =
        (y : G) * MulAut.conj t y :=
      mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hc y.property)
        _ (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)
    change MulAut.conj t ((y : G) * MulAut.conj t y) = _
    rw [map_mul, htwice]
    exact hcomm
  have hd : d.range ≤ ComponentTransfer.centralizerIn I t := by
    rintro _ ⟨y, rfl⟩
    constructor
    · rw [hI]
      exact (J ⊔ J.conjBy t).mul_mem
        ((le_sup_left : J ≤ J ⊔ J.conjBy t) y.property)
        ((le_sup_right : J.conjBy t ≤ J ⊔ J.conjBy t)
          (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property))
    · apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun z : G => z * t) (hfix y)
      simpa only [MulAut.conj_apply, inv_mul_cancel_right] using he.symm
  exact le_map_solvableResidual_of_isPerfect d.range
    (ComponentTransfer.centralizerIn I t) hd ⟨x, rfl⟩

private theorem centralizes_of_diagonal {A J L : Subgroup G} {t : G}
    [IsQuasisimple J] (hc : ⁅J, J.conjBy t⁆ = ⊥)
    (hAJ : A ≤ normalizer J) (hAt : A ≤ centralizer ({t} : Set G))
    (hAL : A ≤ centralizer (L : Set G))
    (hd : ∀ x : J, (x : G) * MulAut.conj t x ∈ L) :
    A ≤ centralizer (J : Set G) := by
  have hcomm : ⁅A, J⁆ ≤ J.conjBy t := by
    apply commutator_le.mpr
    intro a ha x hx
    have hat : Commute a t := mem_centralizer_singleton_iff.mp (hAt ha)
    have hax : MulAut.conj a x ∈ J := (mem_normalizer_iff.mp (hAJ ha) x).mp hx
    have hcommAut : MulAut.conj a (MulAut.conj t x) =
        MulAut.conj t (MulAut.conj a x) := by
      exact congrArg (fun f : MulAut G => f x) (hat.map MulAut.conj).eq
    have hk : MulAut.conj a (MulAut.conj t x) ∈ J.conjBy t := by
      rw [hcommAut]
      exact mem_map_of_mem (MulAut.conj t).toMonoidHom hax
    have heq : MulAut.conj a x * MulAut.conj a (MulAut.conj t x) =
        x * MulAut.conj t x := by
      rw [← map_mul]
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_iff.mp (hAL ha) _ (hd ⟨x, hx⟩)).symm
    have heq' : x⁻¹ * MulAut.conj a x =
        MulAut.conj t x * (MulAut.conj a (MulAut.conj t x))⁻¹ := by
      apply eq_mul_inv_iff_mul_eq.mpr
      rw [mul_assoc, heq, inv_mul_cancel_left]
    have hdiff : x⁻¹ * MulAut.conj a x ∈ J.conjBy t := heq' ▸
      (J.conjBy t).mul_mem (mem_map_of_mem (MulAut.conj t).toMonoidHom hx)
        ((J.conjBy t).inv_mem hk)
    have hdiffcomm : (x⁻¹ * MulAut.conj a x) * x =
        x * (x⁻¹ * MulAut.conj a x) :=
      mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc hx) _ hdiff
    have helem : ⁅a, x⁆ = x⁻¹ * MulAut.conj a x := by
      apply mul_right_cancel (b := x)
      simpa only [commutatorElement_def, inv_mul_cancel_right, mul_inv_cancel_left,
        MulAut.conj_apply] using hdiffcomm.symm
    exact helem ▸ hdiff
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  exact le_bot_iff.mp ((commutator_mono hcomm le_rfl).trans
    (by simpa only [commutator_comm] using hc.le))

/-- The swapped branch is impossible for the order-four component hypothesis,
using the literal earlier solvable-residual equality. -/
theorem not_swapped [Finite G] {E L : Subgroup G} {t i : G}
    (hcard : Nat.card E = 4) (hc : CentralizesAsComponent E L)
    (hEL : E ≤ centralizer (L : Set G)) (htE : t ∈ E) (ht : orderOf t = 2)
    (_hi : orderOf i = 2) (hiC : i ∈ centralizer ((E ⊔ L : Subgroup G) : Set G))
    (hswap : ComponentTransfer.SwappedComponents (involutionCentralizer i) t L
      (ComponentTransfer.layerClosure (involutionCentralizer i) L))
    (hres : L = ComponentTransfer.centralizerResidual
      (ComponentTransfer.layerClosure (involutionCentralizer i) L) t) : False := by
  let I := ComponentTransfer.layerClosure (involutionCentralizer i) L
  have hEH : E ≤ involutionCentralizer i := by
    intro e he
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hiC e ((le_sup_left : E ≤ E ⊔ L) he))
  obtain ⟨J, hJ, hne, hI, hJJ, _⟩ := hswap.commute (hEH htE)
  change I = J ⊔ J.conjBy t at hI
  let _ : IsQuasisimple J := hJ.quasisimple
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hd (x : J) : (x : G) * MulAut.conj t x ∈ L := by
    rw [hres]
    exact diagonal_mem_residual hI ht2 hJJ x
  have hn : E ≤ normalizer I := normalizes_enlargement hEL hiC
  obtain ⟨e, heE, he1, heN⟩ := exists_nontrivial_normalizer hcard htE hEH hJ hI hn
  let _ : IsMulCommutative E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hcard)
  have hEt : E ≤ involutionCentralizer t := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨t, htE⟩))
  let A := E ⊓ normalizer J
  have hAC : A ≤ centralizer (J : Set G) := centralizes_of_diagonal hJJ
    inf_le_right (inf_le_left.trans hEt) (inf_le_left.trans hEL) hd
  have heJ : e ∈ centralizer (J : Set G) := hAC ⟨heE, heN⟩
  have het : Commute e t := mem_centralizer_singleton_iff.mp (hEt heE)
  have hIC : I ≤ involutionCentralizer e := by
    rw [hI]
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp heJ x hx)
    · rintro _ ⟨x, hx, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have hex : Commute e x := (show Commute x e from mem_centralizer_iff.mp heJ x hx).symm
      exact ((het.mul_right hex).mul_right het.inv_right).symm.eq
  have hLC : Theory.GroupTheory.IsComponentIn L I :=
    (show Theory.GroupTheory.IsComponentIn L (involutionCentralizer e) from hc e heE he1).restrict
      (ComponentTransfer.le_layerClosure _ _) hIC
  have hJC : Theory.GroupTheory.IsComponentIn J I :=
    (show Theory.GroupTheory.IsComponentIn J (involutionCentralizer i) from hJ).restrict
      (hI.symm ▸ le_sup_left) (hI.symm ▸ sup_le hJ.1 (hJ.conjugate (hEH htE)).1)
  have hLne : L ≠ J := by
    intro heq
    have htC : t ∈ centralizer (J : Set G) := heq ▸ hEL htE
    exact hne (mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ htC)).symm
  have hLJ : ⁅L, J⁆ = ⊥ := hLC.commutator_eq_bot_of_ne hJC hLne
  have hself : J ≤ centralizer (J : Set G) := by
    intro x hx
    apply mem_centralizer_iff.mpr
    intro y hy
    have hdy : Commute (x * MulAut.conj t x) y :=
      (show Commute y (x * MulAut.conj t x) from mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hLJ (hd ⟨x, hx⟩)) y hy).symm
    have hsy : Commute (MulAut.conj t x) y := mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hJJ hy) _
      (mem_map_of_mem (MulAut.conj t).toMonoidHom hx)
    have hxy := hdy.mul_left hsy.inv_left
    simpa only [mul_inv_cancel_right] using hxy.symm.eq
  have hzero : J = ⊥ := by
    simpa only [commutator_eq_self] using commutator_eq_bot_iff_le_centralizer.mpr hself
  exact (show Theory.GroupTheory.IsComponentIn J (involutionCentralizer i) from hJ).ne_bot hzero

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.Swapped
