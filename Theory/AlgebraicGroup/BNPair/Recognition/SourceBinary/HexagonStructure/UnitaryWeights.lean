module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryDerivedRoots
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CenterIrreducibility
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryRootDerived
public import Theory.SpecificGroups.SU3.BinaryRootFrattini.Images
public import Theory.Representation.FiniteSimpleGenerators

/-!
# Unitary Cartan constituents in the actual hexagon radical

The full normalizer of a unitary Sylow leaves no proper subgroup outside
its Frattini subgroup. Transport through the literal endpoint action gives
the same dichotomy for each canonical root, and hence irreducibility of
its quadratic-dimensional binary Frattini quotient. Its Frattini subgroup
is exactly its intrinsic center, of fixed-field order.

The five root maps generate the actual radical Frattini module. Odd-Cartan
semisimplicity therefore gives the subset-sum dimensions of all invariant
sections and identifies every irreducible section with a root constituent.
A surviving irreducible root constituent injects into that module; its
intersection with the radical Frattini subgroup is exactly its own Frattini
subgroup. No independence of the five images is assumed.

Source: Fong--Seitz I (6D), printed p.42, with the root actions of (3G)
and the full-torus coordinate calculation in BinaryRootFrattini.Images.
This proves the Cartan constituent step; the parameter equality and
lower-central-series contradiction remain separate obligations.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped IsMulCommutative Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates ReeSource HermitianForm QuadrangleStructure

private theorem unitary_sylow_normalized_square_dichotomy
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hf : Nat.card {x : E // J.conj x=x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (W : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hW : W ≤ T)
    (hN : normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      normalizer (W : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    (∀ x ∈ W, x^2 = 1) ∨ W = (T : Subgroup _) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let U := EvenTwoRank.rootSylow J hJ (by omega : 0<n) hcard hf
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) T U
  let e := MulAut.conj g
  have hT : (T : Subgroup _).map e.toMonoidHom = BorelTorus.projectiveRoot J hJ :=
    congrArg Sylow.toSubgroup hg
  have hnW : BorelTorus.projectiveTorus J hJ ≤ normalizer (W.map e.toMonoidHom : Set _) := by
    apply (unitary_torus_normalizes_root J hJ).trans
    rw [←hT,←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
    exact map_mono hN
  have hwW : W.map e.toMonoidHom ≤ BorelTorus.projectiveRoot J hJ := hT ▸ map_mono hW
  have hq : 2 < 2^n := (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
  rcases BinaryRootFrattini.projective_invariant_subgroup J hJ hcard hf hq
    (W.map e.toMonoidHom) hwW hnW with hs | he
  · left
    let c : BorelTorus.projectiveRoot J hJ ≃* hermitianUnipotentCoord J :=
      (MonoidHom.ofInjective (EvenInner.root_injective J hJ)).symm
    have hc := (BinaryRootFrattini.equiv_structure J hcard hf c).1
    intro x hx
    obtain ⟨z,hz,he⟩ := hs (mem_map_of_mem e.toMonoidHom hx)
    have hz2 : z^2=1 := (hc z).mp hz
    apply e.injective
    change (z : ProjectiveSpecialUnitaryMatrixGroup J) = e x at he
    rw [map_pow,map_one,←he]
    exact congrArg Subtype.val hz2
  · exact Or.inr (Subgroup.map_injective e.injective (he.trans hT.symm))

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem simpleRoot_normalized_square_dichotomy {M : Type*} [Group M]
    (hmodel : ∀ (T : Sylow 2 M) (W : Subgroup M), W ≤ T →
      normalizer (T : Set M) ≤ normalizer (W : Set M) →
      (∀ x ∈ W, x^2=1) ∨ W=(T : Subgroup M))
    (i : Fin 2) (μ : localGroup Q split i ≃* M)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ simpleRoot Q split i)
    (hAN : simpleRoot Q split i ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    (∀ x ∈ A, x^2=1) ∨ A=simpleRoot Q split i := by
  let C := localClosure Q split i
  let V := simpleRemainder Q split i
  let W := A ⊔ V
  have hUC : split.U ≤ C := le_sup_left
  have hVC : V ≤ C := inf_le_left.trans hUC
  have hAC : A ≤ C := hA.trans ((simpleRoot_le Q split i).trans hUC)
  have hWU : W ≤ split.U := sup_le (hA.trans (simpleRoot_le Q split i)) inf_le_left
  have hsup : simpleRoot Q split i ⊔ V = split.U := by
    apply le_antisymm (sup_le (simpleRoot_le Q split i) inf_le_left)
    intro x hx
    have hx' : x ∈ (simpleRoot Q split i : Set (X ⧸ Q.D)) * (V : Set (X ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]; exact hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hx'
    exact mul_mem_sup ha hb
  have hB : Q.tits.B ≤ normalizer (W : Set (X ⧸ Q.D)) := by
    have hVP := remainder_parabolic_normalizes Q split i hV
    have hUN : simpleRoot Q split i ≤ normalizer (W : Set (X ⧸ Q.D)) :=
      (le_inf hAN ((simpleRoot_le Q split i).trans
        (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hVP)))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hVN : V ≤ normalizer (W : Set (X ⧸ Q.D)) := le_sup_right.trans W.le_normalizer
    have hHU : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) :=
      (le_inf hH (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans hVP))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    rw [←split.factorization,←hsup]
    exact sup_le (sup_le hUN hVN) hHU
  let T : Sylow 2 C := split.sylow.subtype hUC
  let f : C →* M := μ.toMonoidHom.comp (localAction Q split i).rangeRestrict
  have hf : Function.Surjective f := μ.surjective.comp (MonoidHom.rangeRestrict_surjective _)
  have hk (c : C) : f c = 1 ↔ (c : X ⧸ Q.D) ∈ localKernel Q i := by
    have hμ : f c = 1 ↔ (localAction Q split i).rangeRestrict c = 1 := μ.map_eq_one_iff
    rw [hμ,Subtype.ext_iff]
    change c ∈ (localAction Q split i).ker ↔ _
    rw [localAction_ker]; rfl
  have hnormal : normalizer (T : Set C) ≤ normalizer (W.subgroupOf C : Set C) := by
    change normalizer (split.U.subgroupOf C : Set C) ≤ _
    rw [←subgroupOf_normalizer_eq hUC,split.normalizer_eq]
    exact (comap_mono hB).trans (W.le_normalizer_comap C.subtype)
  have hVmap : (V.subgroupOf C).map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro v hv
    exact (hk v).mpr (hV hv)
  have hroot : ((simpleRoot Q split i).subgroupOf C).map f = (T : Subgroup C).map f := by
    change _ = (split.U.subgroupOf C).map f
    rw [←hsup,subgroupOf_sup ((simpleRoot_le Q split i).trans hUC) hVC,
      Subgroup.map_sup,hVmap,sup_bot_eq]
  have hWA : (W.subgroupOf C).map f = (A.subgroupOf C).map f := by
    rw [show W=A⊔V from rfl,subgroupOf_sup hAC hVC,Subgroup.map_sup,hVmap,sup_bot_eq]
  have hd := hmodel (T.mapSurjective hf) ((W.subgroupOf C).map f)
    (map_mono (subgroupOf_mono C hWU)) (by
      change normalizer ((T : Subgroup C).map f : Set M) ≤ _
      rw [←T.normalizer_map_surjective f hf]
      exact (map_mono hnormal).trans ((W.subgroupOf C).le_normalizer_map f))
  rcases hd with hs | he
  · left
    intro a ha
    have hh := hs (f ⟨a,hAC ha⟩) (by rw [hWA]; exact mem_map_of_mem f ha)
    have hk' : a^2 ∈ localKernel Q i := (hk (⟨a,hAC ha⟩^2)).mp (by rwa [map_pow])
    exact (disjoint_iff.mp (simpleRoot_disjoint_localKernel Q split i)).le
      ⟨pow_mem (hA ha) 2,hk'⟩
  · right
    have heqA : (A.subgroupOf C).map f = ((simpleRoot Q split i).subgroupOf C).map f := by
      rw [←hWA,hroot]; exact he
    apply le_antisymm hA
    intro u hu
    have hm : f ⟨u,hUC (simpleRoot_le Q split i hu)⟩ ∈ (A.subgroupOf C).map f := by
      rw [heqA]; exact mem_map_of_mem f hu
    obtain ⟨a,ha,he⟩ := hm
    have hkernel : (a : X ⧸ Q.D)⁻¹*u ∈ localKernel Q i := by
      apply (hk (a⁻¹ * ⟨u,hUC (simpleRoot_le Q split i hu)⟩)).mp
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hone : (a : X ⧸ Q.D)⁻¹*u = 1 :=
      (disjoint_iff.mp (simpleRoot_disjoint_localKernel Q split i)).le
        ⟨(simpleRoot Q split i).mul_mem ((simpleRoot Q split i).inv_mem (hA ha)) hu,hkernel⟩
    exact (inv_mul_eq_one.mp hone).symm ▸ ha

variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
  (hf : Nat.card {x : E // J.conj x=x} = 2^n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

include hn hcard hf hJ

theorem unitary_simpleRoot_normalized_frattini_dichotomy
    (i : Fin 2) (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ simpleRoot Q split i)
    (hAN : simpleRoot Q split i ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    A ≤ (frattini (simpleRoot Q split i)).map (simpleRoot Q split i).subtype ∨
      A=simpleRoot Q split i := by
  rcases simpleRoot_normalized_square_dichotomy Q split
    (unitary_sylow_normalized_square_dichotomy J hn hcard hf hJ) i μ hV A hA hAN hH with hs | he
  · left
    have hphi := (BinaryRootFrattini.equiv_structure J hcard hf
      (simpleRootUnitaryEquiv J Q split (by omega) hcard hf hJ i hV μ)).1
    intro a ha
    exact mem_map_of_mem (simpleRoot Q split i).subtype
      ((hphi ⟨a,hA ha⟩).mpr (Subtype.ext (hs a ha)))
  · exact Or.inr he

/-- The normalized-subgroup dichotomy on every literal Weyl-conjugate root. -/
theorem unitary_rootAt_normalized_frattini_dichotomy
    (i : Fin 2) (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (w : Weyl Q)
    (A : Subgroup (X ⧸ Q.D)) (hA : A ≤ rootAt Q split i w)
    (hAN : rootAt Q split i w ≤ normalizer (A : Set (X ⧸ Q.D)))
    (hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A : Set (X ⧸ Q.D))) :
    A ≤ (frattini (rootAt Q split i w)).map (rootAt Q split i w).subtype ∨
      A=rootAt Q split i w := by
  let a := (MulAut.conj (representative w : X ⧸ Q.D))
  let A' := A.map a.toMonoidHom
  have hroot : (rootAt Q split i w).map a.toMonoidHom = simpleRoot Q split i := by
    change ((simpleRoot Q split i).comap a.toMonoidHom).map a.toMonoidHom = _
    exact map_comap_eq_self_of_surjective a.surjective _
  have hA' : A' ≤ simpleRoot Q split i := hroot ▸ map_mono hA
  have hAN' : simpleRoot Q split i ≤ normalizer (A' : Set (X ⧸ Q.D)) := by
    rw [←hroot,←map_equiv_normalizer_eq]
    exact map_mono hAN
  have hH' : Q.tits.B ⊓ Q.tits.N ≤ normalizer (A' : Set (X ⧸ Q.D)) := by
    rw [←map_equiv_normalizer_eq]
    have hh := map_mono (f := a.toMonoidHom) hH
    have heH : (Q.tits.B ⊓ Q.tits.N).map a.toMonoidHom = Q.tits.B ⊓ Q.tits.N :=
      mem_normalizer_iff_map_conj_eq.mp (torus_normalizes (representative w))
    rwa [heH] at hh
  rcases unitary_simpleRoot_normalized_frattini_dichotomy Q split J hn hcard hf hJ
    i μ hV A' hA' hAN' hH' with hs | he
  · left
    apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    rw [BinaryRootFrattini.frattini_image_map,hroot]
    exact hs
  · exact Or.inr (Subgroup.map_injective a.injective (he.trans hroot.symm))

/-- The actual root Frattini quotient has quadratic-field order. -/
theorem unitary_rootAt_frattini_card
    (i : Fin 2) (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (w : Weyl Q) :
    Nat.card (rootAt Q split i w ⧸ frattini (rootAt Q split i w)) = 2^(2*n) := by
  let e : rootAt Q split i w ≃* hermitianUnipotentCoord J :=
    (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)).trans
    (simpleRootUnitaryEquiv J Q split (by omega) hcard hf hJ i hV μ)
  let a := QuotientGroup.congr _ _ e (frattini_map_equiv e)
  rw [Nat.card_congr a.toEquiv,BinaryRootFrattini.frattini_eq_first_kernel J hcard hf]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (BinaryRootFrattini.firstCoordinate J)
    (BinaryRootFrattini.firstCoordinate_surjective J hcard hf)).toEquiv,
    Nat.card_congr Multiplicative.toAdd,hcard,←pow_mul,Nat.mul_comm n 2]

/-- The full Cartan acts irreducibly on the literal root Frattini quotient. -/
theorem unitary_rootAt_cartan_frattini_irreducible
    (i : Fin 2) (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (w : Weyl Q) :
    (rootAtCartanFrattiniRepresentation Q split i w).IsIrreducible ∧
      Module.finrank (ZMod 2)
        (Additive (rootAt Q split i w ⧸ frattini (rootAt Q split i w))) = 2*n := by
  let A := rootAt Q split i w
  let π := QuotientGroup.mk' (frattini A)
  let ρ := rootAtCartanFrattiniRepresentation Q split i w
  have hc := unitary_rootAt_frattini_card Q split J hn hcard hf hJ i μ hV w
  let : Nontrivial (A ⧸ frattini A) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hc]; exact Nat.one_lt_two_pow (by omega))
  have hir : ρ.IsIrreducible := by
    refine { eq_bot_or_eq_top := ?_ }
    intro S
    let D : Subgroup (A ⧸ frattini A) := S.toSubmodule.toAddSubgroup.toSubgroup'
    let W := (D.comap π).map A.subtype
    have hWA : W ≤ A := map_subtype_le _
    have hAW : A ≤ normalizer (W : Set (X ⧸ Q.D)) := by
      apply le_normalizer_iff.mpr
      intro a ha x hx
      obtain ⟨v,hv,rfl⟩ := hx
      refine ⟨(⟨a,ha⟩ : A)*v*(⟨a,ha⟩ : A)⁻¹,?_,rfl⟩
      change π (_*_*_) ∈ D
      rw [map_mul,map_mul,map_inv,mul_comm (π ⟨a,ha⟩),mul_inv_cancel_right]
      exact hv
    have hHW : Q.tits.B ⊓ Q.tits.N ≤ normalizer (W : Set (X ⧸ Q.D)) := by
      apply le_normalizer_iff.mpr
      intro h hh x hx
      obtain ⟨v,hv,rfl⟩ := hx
      refine ⟨rootAction Q split i w ⟨h,hh⟩ v,?_,rfl⟩
      have hs := S.apply_mem_toSubmodule ⟨h,hh⟩ hv
      change Additive.ofMul ((quotientAut (frattini A))
        (rootAction Q split i w ⟨h,hh⟩) (π v)) ∈ S at hs
      rw [quotientAut_apply_mk] at hs
      exact hs
    rcases unitary_rootAt_normalized_frattini_dichotomy Q split J hn hcard hf hJ
      i μ hV w W hWA hAW hHW with hs | he
    · left
      apply le_antisymm _ bot_le
      intro v hv
      obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (frattini A) v.toMul
      have hxW : (x : X ⧸ Q.D) ∈ W := mem_map_of_mem A.subtype (show π x ∈ D by
        change Additive.ofMul (π x) ∈ S
        rwa [hx])
      have hxPhi := (mem_map_iff_mem A.subtype_injective).mp (hs hxW)
      have hx1 := (QuotientGroup.eq_one_iff _).mpr hxPhi
      exact Additive.toMul.injective (hx.symm.trans hx1)
    · right
      apply top_unique
      intro v _
      obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (frattini A) v.toMul
      have hxW : (x : X ⧸ Q.D) ∈ W := he ▸ x.property
      have hh := (mem_map_iff_mem A.subtype_injective).mp hxW
      change Additive.ofMul (π x) ∈ S at hh
      rwa [hx] at hh
  refine ⟨hir,?_⟩
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (A ⧸ frattini A))
  rw [Nat.card_zmod] at hd
  change Nat.card (A ⧸ frattini A) = _ at hd
  rw [hc] at hd
  exact (Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hd).symm

/-- The smaller Cartan layer is the whole intrinsic center, of fixed-field order. -/
theorem unitary_rootAt_frattini_center
    (i : Fin 2) (μ : localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (w : Weyl Q) :
    frattini (rootAt Q split i w) = center (rootAt Q split i w) ∧
      Nat.card (frattini (rootAt Q split i w)) = 2^n := by
  let A := rootAt Q split i w
  let e : A ≃* hermitianUnipotentCoord J :=
    (RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)).trans
      (simpleRootUnitaryEquiv J Q split (by omega) hcard hf hJ i hV μ)
  have hAc : Nat.card A = (2^n)^3 := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (MonoidHom.ofInjective (EvenInner.root_injective J hJ)).toEquiv]
    exact OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J hJ _ hcard hf
  have hq := unitary_rootAt_frattini_card Q split J hn hcard hf hJ i μ hV w
  have hc : Nat.card (frattini A) = 2^n := by
    have hh := (frattini A).index_mul_card
    change Nat.card (A ⧸ frattini A)*Nat.card (frattini A) = Nat.card A at hh
    rw [hq,hAc] at hh
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(2*n))
    rw [hh,←pow_add,←pow_mul]
    congr 1
    omega
  let c : center (hermitianUnipotentCoord J) ≃* Multiplicative (BorelTorus.EvenCenterAction.fixedField J) :=
    (MulEquiv.subgroupCongr (binary_coord_center J (by omega : 0<n) hcard hf)).trans
      (MonoidHom.ofInjective (BorelTorus.EvenCenterAction.centralCoord_injective J)).symm
  have hz : Nat.card (center A) = 2^n :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans
      ((Nat.card_congr c.toEquiv).trans ((Nat.card_congr Multiplicative.toAdd).trans hf))
  exact ⟨eq_of_le_of_card_ge (BinaryRootFrattini.equiv_structure J hcard hf e).2
    (by change Nat.card (center A) ≤ Nat.card (frattini A); rw [hc,hz]),hc⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- An irreducible root Frattini quotient that survives in the radical
injects there; the pre-projection intersection is exactly its Frattini subgroup. -/
theorem root_frattini_intertwiner_injective_and_intersection
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (k : Fin 2) (w : Weyl Q) (hA : rootAt Q split k w ≤ simpleRemainder Q split j)
    (hir : (rootAtCartanFrattiniRepresentation Q split k w).IsIrreducible)
    (hnot : ¬ rootAt Q split k w ≤
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype) :
    Function.Injective (rootFrattiniIntertwiner Q split j hKj k w hA) ∧
      rootAt Q split k w ⊓
          (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        (frattini (rootAt Q split k w)).map (rootAt Q split k w).subtype := by
  let A := rootAt Q split k w
  let V := simpleRemainder Q split j
  let d := radicalSection Q split j hKj
  let f := rootFrattiniIntertwiner Q split j hKj k w hA
  let := hir
  have hinj : Function.Injective f := by
    apply (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right
    intro hf
    apply hnot
    intro a ha
    let x : A := ⟨a,ha⟩
    have hx := congrArg (fun z => z (Additive.ofMul (QuotientGroup.mk x))) hf
    have hz : (QuotientGroup.mk' d.effectiveDenominator) (inclusion hA x) = 1 :=
      congrArg Additive.toMul hx
    have hp := (QuotientGroup.eq_one_iff _).mp hz
    rw [suzuki_radical_effectiveDenominator Q split j hKj] at hp
    exact mem_map_of_mem V.subtype hp
  refine ⟨hinj,le_antisymm ?_ ?_⟩
  · rintro a ⟨ha,hD⟩
    let x : A := ⟨a,ha⟩
    let v : V := inclusion hA x
    have hv : v ∈ d.effectiveDenominator := by
      rw [suzuki_radical_effectiveDenominator Q split j hKj]
      exact (mem_map_iff_mem V.subtype_injective).mp hD
    have he : f (Additive.ofMul (QuotientGroup.mk x)) = f 0 := by
      rw [map_zero]
      apply Additive.toMul.injective
      exact (QuotientGroup.eq_one_iff _).mpr hv
    have hx : (QuotientGroup.mk' (frattini A)) x = 1 :=
      congrArg Additive.toMul (hinj he)
    exact mem_map_of_mem A.subtype ((QuotientGroup.eq_one_iff _).mp hx)
  · refine le_inf (map_subtype_le _) ?_
    let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
    rintro _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem V.subtype (frattini_map_le_of_isPGroup (p := 2) (inclusion hA)
      (mem_map_of_mem _ hx))

set_option backward.isDefEq.respectTransparency false in
/-- Odd Cartan semisimplicity transports the five actual simple root
constituents to every invariant subquotient of the radical Frattini module. -/
theorem radical_section_dimension_of_root_profile (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (d : Fin 5 → ℕ)
    (hprofile : ∀ t : Fin 5,
      (rootAtCartanFrattiniRepresentation Q split
        (radicalRootKind i j t) (radicalRootWord Q i j t)).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive
        (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⧸
          frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)))) = d t)
    (U : Subrepresentation (radicalHRepresentation Q split j hKj))
    (N : Subrepresentation U.toRepresentation) :
    ∃ s : Finset (Fin 5), Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = ∑ t ∈ s, d t := by
  classical
  let ρ := radicalHRepresentation Q split j hKj
  let σ := N.quotientRepresentation
  have hc : Representation.IsCompletelyReducible ρ :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime ρ (Or.inr (by
      rw [ringChar.eq (ZMod 2) 2]; exact ⟨Nat.prime_two,split.odd⟩))
  obtain ⟨p,hp⟩ := Representation.section_surjection_of_completelyReducible ρ U N hc
  let f (t : Fin 5) := radicalRootIntertwiner Q split hhex i j hij hKj t
  let g (t : Fin 5) := p.comp (f t)
  let J : Subrepresentation σ := ⨆ t, (g t).range
  let A : Subrepresentation ρ := {
    toSubmodule := J.toSubmodule.comap p.toLinearMap
    apply_mem_toSubmodule h v hv := by
      change p (ρ h v) ∈ J.toSubmodule
      rw [p.isIntertwining]
      exact J.apply_mem_toSubmodule h hv }
  have hA : A = ⊤ := by
    apply top_unique
    rw [← radical_root_intertwiners_span Q split hhex i j hij hKj]
    apply iSup_le
    intro t v hv
    obtain ⟨x,rfl⟩ := hv
    change p (f t x) ∈ J
    have hle : (g t).range ≤ J := by
      dsimp only [J]; exact le_iSup (fun u => (g u).range) t
    exact hle ⟨x,rfl⟩
  have hJ : J = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨v,rfl⟩ := hp y
    exact (show v ∈ A from hA ▸ Submodule.mem_top)
  let V (t : Fin 5) := Additive
    (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⧸
      frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)))
  let τ (t : Fin 5) := rootAtCartanFrattiniRepresentation Q split
    (radicalRootKind i j t) (radicalRootWord Q i j t)
  obtain ⟨s,_,hd⟩ := Representation.finrank_simple_generators V τ σ
    (fun t => (hprofile t).1)
    g Finset.univ
  have hspan : (⨆ t ∈ (Finset.univ : Finset (Fin 5)), (g t).range) = ⊤ := by
    simpa only [Finset.mem_univ,iSup_pos] using hJ
  rw [hspan] at hd
  change Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) (U ⧸ N.toSubmodule)) = _ at hd
  rw [finrank_top] at hd
  refine ⟨s,hd.trans ?_⟩
  exact Finset.sum_congr rfl fun t _ =>
    (hprofile t).2

set_option backward.isDefEq.respectTransparency false in
/-- Every irreducible Cartan section is an actual simple root constituent,
with exactly its binary dimension. -/
theorem radical_irreducible_section_dimension_of_root_profile (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (d : Fin 5 → ℕ)
    (hprofile : ∀ t : Fin 5,
      (rootAtCartanFrattiniRepresentation Q split
        (radicalRootKind i j t) (radicalRootWord Q i j t)).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive
        (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⧸
          frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)))) = d t)
    (U : Subrepresentation (radicalHRepresentation Q split j hKj))
    (N : Subrepresentation U.toRepresentation) (hN : N.quotientRepresentation.IsIrreducible) :
    ∃ t : Fin 5, Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = d t := by
  let ρ := radicalHRepresentation Q split j hKj
  have hc : Representation.IsCompletelyReducible ρ :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime ρ (Or.inr (by
      rw [ringChar.eq (ZMod 2) 2]; exact ⟨Nat.prime_two,split.odd⟩))
  obtain ⟨p,hp⟩ := Representation.section_surjection_of_completelyReducible ρ U N hc
  let f (t : Fin 5) := radicalRootIntertwiner Q split hhex i j hij hKj t
  have hsome : ∃ t, p.comp (f t) ≠ 0 := by
    by_contra! hh
    have hker : p.ker = ⊤ := by
      apply top_unique
      rw [←radical_root_intertwiners_span Q split hhex i j hij hKj]
      apply iSup_le
      intro t v hv
      obtain ⟨x,rfl⟩ := hv
      exact DFunLike.congr_fun (hh t) x
    let := hN
    let : Nontrivial (U ⧸ N.toSubmodule) :=
      Subrepresentation.irreducible_module_nontrivial N.quotientRepresentation
    obtain ⟨v,hv⟩ := exists_ne (0 : U ⧸ N.toSubmodule)
    obtain ⟨x,rfl⟩ := hp v
    exact hv (show x ∈ p.ker from hker ▸ Submodule.mem_top)
  obtain ⟨t,ht⟩ := hsome
  let := (hprofile t).1
  let := hN
  have hb := (Representation.IsIrreducible.bijective_or_eq_zero (p.comp (f t))).resolve_right ht
  exact ⟨t,(LinearEquiv.ofBijective (p.comp (f t)).toLinearMap hb).finrank_eq.symm.trans
    (hprofile t).2⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure


open Subgroup
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- The whole radical quotient has the dimension of a subfamily of its five actual root constituents. -/
theorem radical_dimension_of_root_profile (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (d : Fin 5 → ℕ)
    (hprofile : ∀ t : Fin 5,
      (rootAtCartanFrattiniRepresentation Q split
        (radicalRootKind i j t) (radicalRootWord Q i j t)).IsIrreducible ∧
      Module.finrank (ZMod 2) (Additive
        (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t) ⧸
          frattini (rootAt Q split (radicalRootKind i j t) (radicalRootWord Q i j t)))) = d t) :
    ∃ s : Finset (Fin 5), Module.finrank (ZMod 2)
      (Additive (radicalSection Q split j hKj).EffectiveCarrier) = ∑ t ∈ s, d t := by
  let ρ := radicalHRepresentation Q split j hKj
  let U : Subrepresentation ρ := ⊤
  let N : Subrepresentation U.toRepresentation := ⊥
  obtain ⟨s,hs⟩ := radical_section_dimension_of_root_profile Q split hhex i j hij hKj
    d hprofile U N
  have he : Module.finrank (ZMod 2) (U ⧸ N.toSubmodule) = Module.finrank (ZMod 2)
      (Additive (radicalSection Q split j hKj).EffectiveCarrier) :=
    (Submodule.quotEquivOfEqBot N.toSubmodule rfl).finrank_eq.trans
      Submodule.topEquiv.finrank_eq
  exact ⟨s,he.symm.trans hs⟩

/-- The unitary degree minimum leaves these three five-root weight sums when m < n. -/
theorem unequal_unitary_weight_sum {m n d : ℕ} (hmn : m < n) (hlo : 6*n ≤ d)
    (s : Finset (Fin 5))
    (hs : d = ∑ t ∈ s, if t = 1 ∨ t = 3 then 2*n else 2*m) :
    d = 6*m+2*n ∨ d = 4*m+4*n ∨ d = 6*m+4*n := by
  classical
  have he : (∑ t ∈ s, if t = 1 ∨ t = 3 then 2*n else 2*m) =
      ∑ t : Fin 5, if t ∈ s then (if t = 1 ∨ t = 3 then 2*n else 2*m) else 0 := by
    simp
  rw [he,Fin.sum_univ_five] at hs
  simp only [Fin.reduceEq,or_false,false_or,or_self,ite_false,ite_true] at hs
  split_ifs at hs <;> omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
