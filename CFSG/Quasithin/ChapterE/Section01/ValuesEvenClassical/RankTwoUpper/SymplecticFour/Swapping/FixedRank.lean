module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.DiagramKernel
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.Parity
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.Basic
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.CenterCount
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.CenterPlacement
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Fixed-actor rank from the actual central roots

For an elementary subgroup A in the diagram kernel, map A to the genuine
outer automorphism quotient of its marked symplectic socle. Its image has
order at most two by outer cyclicity and divides the field degree by diagram
preservation. In odd degree the image is trivial. The kernel embeds in Sp₄(F)
through the original socle marking, and in the actual Sylow T ∩ L.

A central placement calculation for fixed involutions then embeds this kernel
in the fixed Sylow center. The required center count is q in all degrees,
and its square is at most q in even degree. These two estimates absorb the
possible order-two outer image and prove rank(A) ≤ f. Applying the existing
tau reduction gives the literal E.1.2(E0) containment for larger actors.

The conditional assembly is retained as an interface for the two independent
central-root calculations. The final theorems supply both proved calculations,
giving the unconditional fixed-rank bound and tau containment. They cover every
swapping actor in T, including arbitrary two-power orders and inner twists.
The rank bound uses neither SQTK nor the Sylow supplement hypothesis; the
supplement is used only to identify the literal ambient tau in its application.

Source: Aschbacher--Smith E.1.1--2 and E.1.14(1), printed pp.209--210,214;
the Sp₄ root coordinates and automorphisms of GLS3 §2.5.
-/

public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
open DiagramAutomorphisms DiagramAutomorphisms.SwappingFixedRank
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem card_range_le_two {X Y : Type*} [Group X] [Group Y]
    [Finite X] [Finite Y] [IsElementaryAbelian 2 X] [IsCyclic Y]
    (φ : X →* Y) : Nat.card φ.range ≤ 2 := by
  classical
  let := Fintype.ofFinite Y
  let j : φ.range → {y : Y // y ^ 2 = 1} := fun y => ⟨y.val, by
    obtain ⟨x, hx⟩ := y.property
    rw [← hx, ← map_pow]
    have hx2 : x ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) x
    rw [hx2, map_one]⟩
  have hj : Function.Injective j := fun _ _ h => Subtype.ext (congrArg (fun z : {y : Y // y ^ 2 = 1} => z.val) h)
  have hc := Nat.card_le_card_of_injective j hj
  have hb := IsCyclic.card_pow_eq_one_le (α := Y) (by decide : 0 < 2)
  exact hc.trans (by simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hb)

private theorem range_card_dvd_degree {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hq : 2 < Nat.card F)
    (ρ : X →* MulAut (Sp F)) (hρ : ∀ x, PreservesDiagram (ρ x)) :
    Nat.card (((QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp ρ).range) ∣ f := by
  let π := (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp ρ
  have hle : π.range ≤ (outerFieldHom (F := F)).range := by
    rw [← outerDiagramAction_ker hq SemilinearClassification.inner_field_of_preservesDiagram]
    rintro _ ⟨x, rfl⟩
    exact (mem_parabolicClassAction_ker_iff hq _).mpr (hρ x)
  exact (card_dvd_of_le hle).trans ((Subgroup.card_range_dvd _).trans
    (card_fieldAut hF).dvd)

private theorem mem_socle_of_inner [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F) (g : G)
    (hi : extensionAction _ e g ∈ MulAut.innerSubgroup (Sp F)) :
    g ∈ generalizedFitting G := by
  obtain ⟨u, hu⟩ := hi
  have hinj := extensionAction_injective _ e
    (SimpleSocle.centralizer_eq_bot (symplectic_socle_nonabelian e hq))
  have he : g = (e u).val := hinj (hu.symm.trans
    (extensionAction_model_element _ e u).symm)
  exact he.symm ▸ (e u).property

/-- Conditional assembly from central placement and the two precise fixed-center
counts. The outer image has order at most two, and divides the field degree
when every actor preserves the diagram. -/
theorem rank_le_of_central_root_calculations {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (hplacement : ∀ (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)),
      (S : Subgroup (Sp F)).map a.toMonoidHom = S → ¬ PreservesDiagram a →
      ∀ u ∈ (S : Subgroup (Sp F)), u ^ 2 = 1 → a u = u →
        u ∈ (center S).map (S : Subgroup (Sp F)).subtype)
    (hcount : ∀ (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)),
      (S : Subgroup (Sp F)).map a.toMonoidHom = S → ¬ PreservesDiagram a →
      Nat.card (fixedCenter S a) ≤ Nat.card F ∧
        (Even f → Nat.card (fixedCenter S a) ^ 2 ≤ Nat.card F))
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAH : A ≤ diagramKernel _ e hq)
    (x : G) (hxT : x ∈ (T : Subgroup G))
    (hx : ¬ PreservesDiagram (extensionAction _ e x))
    (hcx : x ∈ centralizer (A : Set G)) : Group.rank A ≤ f := by
  let := hA
  let L := generalizedFitting G
  let ρ := extensionAction L e
  let π : A →* MulAut.Outer (Sp F) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp (ρ.comp A.subtype)
  let : IsCyclic (MulAut.Outer (Sp F)) := outer_isCyclic hF hf
  have himage : Nat.card π.range ≤ 2 := card_range_le_two π
  have hdiv : Nat.card π.range ∣ f := range_card_dvd_degree hF hq (ρ.comp A.subtype)
    (fun a => (mem_diagramKernel_iff L e hq a).mp (hAH a.property))
  have hcard : Nat.card A = Nat.card π.range * Nat.card π.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange π).toEquiv]
  let k : π.ker →* Sp F := e.symm.toMonoidHom.comp {
    toFun := fun a => ⟨a.val.val, mem_socle_of_inner e hq a.val.val
      ((QuotientGroup.eq_one_iff _).mp a.property)⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hk (a : π.ker) : (e (k a)).val = a.val.val := by
    dsimp [k]
    rw [e.apply_symm_apply]
  have hki : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact (hk a).symm.trans ((congrArg (fun u : Sp F => (e u).val) hab).trans (hk b))
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal L
  let S : Sylow 2 (Sp F) := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hS (u : Sp F) : u ∈ (S : Subgroup (Sp F)) ↔ (e u).val ∈ (T : Subgroup G) := by
    change u ∈ (P : Subgroup L).map e.symm.toMonoidHom ↔ _
    rw [hP]
    constructor
    · rintro ⟨v, hv, rfl⟩
      change (e (e.symm v)).val ∈ (T : Subgroup G)
      rw [e.apply_symm_apply]
      exact hv
    · intro hu
      exact ⟨e u, hu, e.symm_apply_apply u⟩
  have hstable : (S : Subgroup (Sp F)).map (ρ x).toMonoidHom = S := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u, hu, rfl⟩
      apply (hS _).mpr
      change (e (extensionAction L e x u)).val ∈ (T : Subgroup G)
      rw [extensionAction_apply]
      exact (T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem hxT ((hS u).mp hu)) ((T : Subgroup G).inv_mem hxT)
    · rw [Subgroup.card_map_of_injective (ρ x).injective]
  have hfix (a : π.ker) : ρ x (k a) = k a := by
    apply e.injective
    apply Subtype.ext
    rw [extensionAction_apply, hk]
    have hc := (mem_centralizer_iff.mp hcx) a.val.val a.val.property
    exact mul_inv_eq_iff_eq_mul.mpr hc.symm
  have hsquare (a : π.ker) : (k a) ^ 2 = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_pow, map_one, coe_pow, coe_one, hk]
    exact elemPow_eq_one_of_isElementaryAbelian a.val.val a.val.property
  let j : π.ker → fixedCenter S (ρ x) := fun a => ⟨k a,
    (mem_fixedCenter S (ρ x) _).mpr ⟨hplacement S (ρ x) hstable hx _
      ((hS _).mpr ((hk a).symm ▸ hAT a.val.property)) (hsquare a) (hfix a), hfix a⟩⟩
  have hker : Nat.card π.ker ≤ Nat.card (fixedCenter S (ρ x)) :=
    Nat.card_le_card_of_injective j (fun _ _ h => hki (congrArg Subtype.val h))
  obtain ⟨hsmall, heven⟩ := hcount S (ρ x) hstable hx
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2) A
  rw [hcard, ← hF]
  rcases Nat.even_or_odd f with he | ho
  · have hs : Nat.card π.ker ^ 2 ≤ Nat.card F :=
      (Nat.pow_le_pow_left hker 2).trans (heven he)
    have hq4 : 4 ≤ Nat.card F := by
      rw [hF]
      exact (show 4 = 2 ^ 2 from rfl) ▸ Nat.pow_le_pow_right (by decide) hf
    have hh : 2 * Nat.card π.ker ≤ Nat.card F := by
      by_cases hk1 : Nat.card π.ker ≤ 1
      · omega
      · nlinarith
    exact (Nat.mul_le_mul_right _ himage).trans hh
  · have hodd : Odd (Nat.card π.range) := ho.of_dvd_nat hdiv
    have hi : Nat.card π.range = 1 := by
      have hp : 0 < Nat.card π.range := Nat.card_pos
      obtain ⟨n, hn⟩ := hodd
      omega
    rw [hi, one_mul]
    exact hker.trans hsmall


/-- Application to the literal ambient tau. Only the independent central-root
placement and count remain to be supplied; the socle, Sylow and quotient
identifications are discharged by the preceding theorem. -/
theorem tau_le_of_central_root_calculations {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (hplacement : ∀ (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)),
      (S : Subgroup (Sp F)).map a.toMonoidHom = S → ¬ PreservesDiagram a →
      ∀ u ∈ (S : Subgroup (Sp F)), u ^ 2 = 1 → a u = u →
        u ∈ (center S).map (S : Subgroup (Sp F)).subtype)
    (hcount : ∀ (S : Sylow 2 (Sp F)) (a : MulAut (Sp F)),
      (S : Subgroup (Sp F)).map a.toMonoidHom = S → ¬ PreservesDiagram a →
      Nat.card (fixedCenter S a) ≤ Nat.card F ∧
        (Even f → Nat.card (fixedCenter S a) ^ 2 ≤ Nat.card F))
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup G))
    (hAH : A ≤ diagramKernel _ e hq) (hr : f < Group.rank A) :
    tau (T : Subgroup G) A ≤ diagramKernel _ e hq := by
  apply tau_le_diagramKernel_of_fixed_rank e hq T hLT ?_ A hA hAT hAH hr
  intro B hB hBT hBH x hxT hx hc
  exact rank_le_of_central_root_calculations hF hf e hq hplacement hcount
    T B hB hBT hBH x hxT hx hc

/-- An elementary subgroup of the diagram kernel centralized by a swapping
Sylow actor has rank at most the field degree. Both central placement and
fixed-center counts are discharged for the original actor, of any order. -/
theorem rank_le_of_swapping_centralizer {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hAH : A ≤ diagramKernel _ e hq)
    (x : G) (hxT : x ∈ (T : Subgroup G))
    (hx : ¬ PreservesDiagram (extensionAction _ e x))
    (hcx : x ∈ centralizer (A : Set G)) : Group.rank A ≤ f := by
  exact rank_le_of_central_root_calculations hF hf e hq
    (fun S a hS ha u hu hu2 hfix => central_placement hF hf S a hS ha hu hu2 hfix)
    (fun S a hS ha => fixedCenter_card_bounds hF hf S a hS ha)
    T A hA hAT hAH x hxT hx hcx

/-- E.1.2(E0) for large elementary actors in the diagram kernel: the actual
ambient tau also lies in that kernel, with no remaining model premise. -/
theorem tau_le_diagramKernel {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAT : A ≤ (T : Subgroup G))
    (hAH : A ≤ diagramKernel _ e hq) (hr : f < Group.rank A) :
    tau (T : Subgroup G) A ≤ diagramKernel _ e hq := by
  exact tau_le_diagramKernel_of_fixed_rank e hq T hLT
    (rank_le_of_swapping_centralizer hF hf e hq T) A hA hAT hAH hr

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.FixedRank
