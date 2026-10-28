module
public import Theory.Representation.BinaryOffender.PermutedSupports
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTransport
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# The Sylow-fixed seed on marked cubic supports

The literal multiplication and addition maps of `SupportFactors` show that
its actors generate the odd core and its natural binary planes are disjoint
and span the module. Distinct canonical actors fix opposite planes. On a
binary plane an order-three actor has no proper moved subspace, by the
fixed-point congruence. Thus any two-group permuting the marked supports
generates the module from its fixed vectors under the odd core.

For three supports, the two-group fixes one actor. The sum of the other two
actors is also normalized, and both actors have nonzero fixed spaces on the
opposite supports. This is the actual placement input in Aschbacher--Smith
15.1.2, printed p.1085. The cross-centralization here corrects the swapped
centralizer labels in the printed paragraph.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
 [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
 theorem plane_separation (X : Subgroup G) (hX : Nat.card X = 3)
    (hU : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2)
    (C : Submodule (ZMod 2) V) (hC : X ≤ subspaceStabilizer ρ C) :
    subspaceCommutator ρ ⊤ X ≤ C ∨ C ≤ fixedSpace ρ X := by
  let U := subspaceCommutator ρ ⊤ X
  let D := subspaceCommutator ρ C X
  have hDU : D ≤ U := subspaceCommutator_mono_left ρ le_top X
  have hDC : D ≤ C := subspaceCommutator_le_of_invariant ρ hC
  have hs : X ≤ subspaceStabilizer ρ D := subspaceCommutator_invariant ρ C X
  have hc := odd_fixed_moved_complement ρ (hX ▸ (by decide : Odd 3))
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : MulAction X D := {
    smul x d := ⟨ρ x d, (hs x.property d).2 d.property⟩
    one_smul d := by apply Subtype.ext; change ρ 1 (d : V) = (d : V); rw [map_one]; rfl
    mul_smul x y d := by apply Subtype.ext; exact congrArg (fun f => f (d : V)) (map_mul ρ (x:G) (y:G)) }
  have hfix : Nat.card (MulAction.fixedPoints X D) = 1 := by
    have he : MulAction.fixedPoints X D ≃ (⊥ : Submodule (ZMod 2) V) :=
      { toFun d := ⟨d.val.val, by
          change d.val.val = 0
          apply Submodule.disjoint_def.mp hc.disjoint
          · exact hDU d.val.property
          · intro x
            exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp d.property x)⟩
        invFun z := ⟨⟨z.val, by rw [show z.val = 0 from z.property]; exact D.zero_mem⟩, by
          intro x
          apply Subtype.ext
          have hz : z.val = 0 := z.property
          change ρ (x : G) z.val = z.val
          rw [hz, map_zero]⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [Nat.card_congr he]
    simp
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hX)).card_modEq_card_fixedPoints D
  rw [hfix] at hm
  have hdim := Submodule.finrank_mono hDU
  change Module.finrank (ZMod 2) D ≤ Module.finrank (ZMod 2) U at hdim
  have hdimU : Module.finrank (ZMod 2) U = 2 := hU
  have hcD : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [hcD] at hm
  have hcases : Module.finrank (ZMod 2) D = 0 ∨ Module.finrank (ZMod 2) D = 2 := by
    have hle : Module.finrank (ZMod 2) D ≤ 2 := hdim.trans_eq hdimU
    interval_cases Module.finrank (ZMod 2) D <;> norm_num [Nat.ModEq] at *
  rcases hcases with h | h
  · right
    exact (subspaceCommutator_eq_bot_iff ρ C X).mp ((Submodule.finrank_eq_zero).mp h)
  · left
    have he : D = U := Submodule.eq_of_le_of_finrank_eq hDU (h.trans hdimU.symm)
    change U ≤ C
    rw [← he]
    exact hDC

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
 theorem SupportFactors.support_disjoint {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) {i j : Fin s} (hne : i ≠ j) :
    Disjoint (subspaceCommutator ρ ⊤ (d.ambient i))
      (subspaceCommutator ρ ⊤ (d.ambient j)) := by
  classical
  apply Submodule.disjoint_def.mpr
  intro v hv hw
  let f : (k : Fin s) → subspaceCommutator ρ ⊤ (d.ambient k) := Pi.single i ⟨v,hv⟩
  let g : (k : Fin s) → subspaceCommutator ρ ⊤ (d.ambient k) := Pi.single j ⟨v,hw⟩
  have hs (k : Fin s) (w : subspaceCommutator ρ ⊤ (d.ambient k)) :
      (∑ l, (((Pi.single k w : (l : Fin s) → subspaceCommutator ρ ⊤ (d.ambient l)) l) : V)) = w := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro l hl hne
      simp [Pi.single_eq_of_ne hne]
    · simp
  have he : (∑ k, (f k : V)) = ∑ k, (g k : V) := by
    exact (hs i ⟨v,hv⟩).trans (hs j ⟨v,hw⟩).symm
  have hh := congrArg (fun x => ((x i : subspaceCommutator ρ ⊤ (d.ambient i)) : V))
    (d.add_bijective.1 he)
  simpa [f,g,hne] using hh

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
 theorem SupportFactors.ambient_injective {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) : Function.Injective d.ambient := by
  intro i j hij
  by_contra hne
  have h := d.support_disjoint ρ hne
  rw [hij] at h
  have he := disjoint_self.mp h
  have hd := d.support_dim j
  change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.ambient j)) = 2 at hd
  rw [he] at hd
  simp at hd

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
 theorem SupportFactors.supports_generate {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) : (⨆ i, subspaceCommutator ρ ⊤ (d.ambient i)) = ⊤ := by
  classical
  apply top_unique
  intro v _
  obtain ⟨w,hw⟩ := d.add_bijective.2 v
  rw [← hw]
  exact Submodule.sum_mem _ (fun i _ => (le_iSup (fun k => subspaceCommutator ρ ⊤ (d.ambient k)) i) (w i).property)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
 theorem SupportFactors.ambients_generate {P : Subgroup G} {s : ℕ}
    (d : SupportFactors ρ P s) : (⨆ i, d.ambient i) = P := by
  classical
  apply le_antisymm (iSup_le fun i => map_subtype_le (d.factor i))
  intro p hp
  obtain ⟨x,hx⟩ := d.multiply_bijective.2 (⟨p,hp⟩ : P)
  have hm : (List.ofFn fun i => ((x i : P) : G)).prod ∈ ⨆ i, d.ambient i := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
    exact (le_iSup (fun i => d.ambient i) i) (mem_map_of_mem P.subtype (x i).property)
  have he : (List.ofFn fun i => ((x i : P) : G)).prod = p := by
    have hh := congrArg (fun z : P => (z : G)) hx
    change P.subtype (List.ofFn fun i => (x i : P)).prod = p at hh
    rw [map_list_prod,List.map_ofFn] at hh
    exact hh
  exact he ▸ hm

 theorem SupportFactors.cross_fixed (hf : Function.Injective ρ) {P : Subgroup G} {s : ℕ}
    [P.Normal] [IsElementaryAbelian 3 P] (d : SupportFactors ρ P s)
    {i j : Fin s} (hne : i ≠ j) :
    subspaceCommutator ρ ⊤ (d.ambient i) ≤ fixedSpace ρ (d.ambient j) := by
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let := Representation.BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hh := smallSupportFactors_cross_fixed (V := Multiplicative V) (Or.inl rfl)
    (d.factor_canonical ρ j) (d.factor_canonical ρ i)
    (fun he => hne ((d.ambient_injective ρ he).symm))
  rw [Representation.BinaryGroupAction.commutator_eq,
      Representation.BinaryGroupAction.fixedPoints_eq] at hh
  exact (Representation.BinaryGroupAction.submoduleEquivSubgroup (V := V)).le_iff_le.mp hh

 theorem SupportFactors.fixed_generates (hf : Function.Injective ρ) {P : Subgroup G} {s : ℕ}
    [P.Normal] [IsElementaryAbelian 3 P] (d : SupportFactors ρ P s)
    (S : Subgroup G) (hS : IsPGroup 2 S) :
    Homogeneous.orbitSpan ρ P (fixedSpace ρ S) = ⊤ := by
  apply PermutedSupports.fixed_generates ρ P S hS d.ambient
    (fun i => subspaceCommutator ρ ⊤ (d.ambient i))
  · intro i
    exact odd_fixed_moved_complement ρ
      (((card_map_of_injective P.subtype_injective).trans (d.card_factor i)) ▸ (by decide : Odd 3))
  · intro i j hij
    exact d.cross_fixed ρ hf hij
  · exact d.supports_generate ρ
  · intro C hC i
    exact plane_separation ρ (d.ambient i)
      ((card_map_of_injective P.subtype_injective).trans (d.card_factor i))
      (d.support_dim i) C ((map_subtype_le _).trans hC)
  · intro g hg i
    obtain ⟨j,hj⟩ := d.factor_conj_closed ρ hf g i
    refine ⟨j, ?_⟩
    rw [moved_map_conjugate]
    exact congrArg (fun K : Subgroup G => subspaceCommutator ρ ⊤ K) hj



 theorem SupportFactors.exists_normalized_split (hf : Function.Injective ρ)
    {P : Subgroup G} [P.Normal] [IsElementaryAbelian 3 P]
    (d : SupportFactors ρ P 3) (S : Subgroup G) (hS : IsPGroup 2 S) :
    ∃ X R : Subgroup G, S ≤ normalizer (X : Set G) ∧
      S ≤ normalizer (R : Set G) ∧ X ⊔ R = P ∧
      fixedSpace ρ X ≠ ⊥ ∧ fixedSpace ρ R ≠ ⊥ := by
  classical
  let F : Set (Subgroup G) := Set.range d.ambient
  let : MulAction S F := {
    smul s X := ⟨X.val.conjBy (s : G), by
      obtain ⟨i,hi⟩ := X.property
      obtain ⟨j,hj⟩ := d.factor_conj_closed ρ hf s i
      exact ⟨j,by rw [← hi]; exact hj.symm⟩⟩
    one_smul X := Subtype.ext (conjBy_one X.val)
    mul_smul s t X := Subtype.ext (conjBy_mul X.val s t) }
  have hc : Nat.card F = 3 := by
    rw [← Nat.card_congr (Equiv.ofInjective d.ambient (d.ambient_injective ρ))]
    simp
  obtain ⟨X,hX⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card F
    (by rw [hc]; decide)
  obtain ⟨i,hi⟩ := X.property
  have hnX : S ≤ normalizer (d.ambient i : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he := congrArg Subtype.val (hX (⟨g,hg⟩ : S))
    change X.val.conjBy g = X.val at he
    rw [← hi] at he
    exact he
  let R : Subgroup G := ⨆ j : Fin 3, ⨆ (_ : j ≠ i), d.ambient j
  have hnR : S ≤ normalizer (R : Set G) := by
    apply subgroup_le_normalizer_of_conj_mem
    intro g y hy
    have hle : R.conjBy (g : G) ≤ R := by
      change (⨆ j : Fin 3, ⨆ (_ : j ≠ i), d.ambient j).map _ ≤ R
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro j
      rw [Subgroup.map_iSup]
      apply iSup_le
      intro hji
      obtain ⟨k,hk⟩ := d.factor_conj_closed ρ hf g j
      change (d.ambient j).conjBy (g : G) ≤ R
      rw [hk]
      have hki : k ≠ i := by
        intro hki
        have he : (d.ambient j).conjBy (g : G) = (d.ambient i).conjBy (g : G) :=
          hk.trans ((congrArg d.ambient hki).trans
            (mem_normalizer_iff_map_conj_eq.mp (hnX g.property)).symm)
        have he' := congrArg (fun Y : Subgroup G => Y.conjBy (g : G)⁻¹) he
        simp only [conjBy_inv] at he'
        exact hji (d.ambient_injective ρ he')
      exact le_iSup_of_le k (le_iSup_of_le hki le_rfl)
    exact hle (mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hy)
  have hgen : d.ambient i ⊔ R = P := by
    apply le_antisymm (sup_le (map_subtype_le _) (iSup_le fun j => iSup_le fun _ => map_subtype_le _))
    apply (d.ambients_generate ρ).ge.trans
    apply iSup_le
    intro j
    by_cases hji : j = i
    · exact hji ▸ le_sup_left
    · have hjR : d.ambient j ≤ R :=
        (le_iSup (fun _ : j ≠ i => d.ambient j) hji).trans
          (le_iSup (fun k : Fin 3 => ⨆ (_ : k ≠ i), d.ambient k) j)
      exact hjR.trans le_sup_right
  have hUi : subspaceCommutator ρ ⊤ (d.ambient i) ≠ ⊥ := by
    intro he
    have hd := d.support_dim i
    change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.ambient i)) = 2 at hd
    rw [he] at hd
    simp at hd
  have hRfix : subspaceCommutator ρ ⊤ (d.ambient i) ≤ fixedSpace ρ R := by
    have hRK : R ≤ subspaceKernel ρ (subspaceCommutator ρ ⊤ (d.ambient i)) ⊤ := by
      apply iSup_le
      intro j
      apply iSup_le
      intro hji g hg
      exact ⟨mem_top _,fun v hv => d.cross_fixed ρ hf hji.symm hv ⟨g,hg⟩⟩
    intro v hv r
    exact (hRK r.property).2 v hv
  obtain ⟨j,hji⟩ : ∃ j : Fin 3, j ≠ i := by
    fin_cases i <;> decide
  have hUj : subspaceCommutator ρ ⊤ (d.ambient j) ≠ ⊥ := by
    intro he
    have hd := d.support_dim j
    change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (d.ambient j)) = 2 at hd
    rw [he] at hd
    simp at hd
  exact ⟨d.ambient i,R,hnX,hnR,hgen,
    fun he => hUj (bot_unique (he ▸ d.cross_fixed ρ hf hji)),
    fun he => hUi (bot_unique (he ▸ hRfix))⟩

end CFSG.Quasithin.ChapterD.FittingConfigurations
