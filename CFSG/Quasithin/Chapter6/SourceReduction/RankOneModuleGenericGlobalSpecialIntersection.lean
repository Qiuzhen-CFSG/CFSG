module
public import Theory.AtlasPort.LinearGroups.G2.LieCoreSpecialness
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRootFusion
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Special-core intersections for the G₂ and triality completions

The five-root G₂ core has a four-dimensional symplectic commutator form.
The triality arms core has an eight-dimensional form over the fixed field,
with its two cubic-field coordinates paired by the actual Frobenius trace.
In either case, the field span of an abelian subgroup's image is isotropic.
The orthogonal dimension formula bounds that span by half the quotient
dimension; retaining the central coordinate gives orders at most q³ and q⁵.
This works for arbitrary abelian subgroups, without assuming that their
images are already vector subspaces over the whole field.

Transport the actual cores through the compatible factor maps. Their
squares lie in Z(K), where K = O²(H). The established TI result makes
Z(K) and Z(K)^g disjoint for g outside N_G(K), so every element of
O₂(K) intersect O₂(K)^g squares to one. The concrete bounds then give
exactly the elementary-intersection estimate in F.4.35 for w = 2 and 4.
The Chapter12 companion applies this to the literal original setup.

The same coordinate maps identify the centralizer of a noncentral point
with a field coordinate times the kernel of a nonzero linear functional,
giving orders q⁴ and q⁸. Once Z(K) lies in Q^g, TI implies that an element
of Q^g fixing one nonidentity point of Z(K) centralizes all of Z(K): its
commutators lie in both Z(K) and the disjoint center of Q^g. This proves
the required whole-root centralizer count. The original Sylow markings
give |S:Q| = q and q³. Together with the intersection bounds, they force
S = Q C_{Q^g}(Z(K)) when that centralizer has been placed in S.

Original uniqueness in Preparation and compatible amalgam comparison
remain inputs. The centralizing root pair, the two Sylow placements,
and the nonfixed short-root action are still needed for nonfusion.
Exhaustive comparison and ambient recognition remain obligations;
no GlobalExit is asserted.
Source: Aschbacher–Smith F.4.35, printed p.292, and F.1.12(I)(3–4),
pp.262–264 (`refs/quasithin.pdf`). G₂ coordinates reuse the existing
licensed ATLAS port (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff);
triality coordinates retain the imported GLS3 root and trace conventions.
-/

public noncomputable section
open Subgroup Module
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace SpecialIntersection

private theorem isotropic_coordinate_bound
    {F V E : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V]
    [Finite E] (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (c : E → F) (v : E → V) (hi : Function.Injective (fun x => (c x,v x)))
    (ho : ∀ x y, B (v x) (v y) = 0) (w : ℕ)
    (hdim : Nat.card V = Nat.card F ^ (2*w)) : Nat.card E ≤ Nat.card F^(w+1) := by
  let W := Submodule.span F (Set.range v)
  have hpair : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨a,rfl⟩ := ha
      induction hy using Submodule.span_induction with
      | mem b hb => obtain ⟨b,rfl⟩ := hb; exact ho a b
      | zero => exact map_zero (B (v a))
      | add b d hb hd hbe hde => rw [map_add,hbe,hde,add_zero]
      | smul t b hb hbe => rw [map_smul,hbe,smul_zero]
    | zero => simp
    | add a b ha hb hae hbe => simp only [map_add,LinearMap.add_apply,hae,hbe,add_zero]
    | smul t a ha hae => simp only [map_smul,LinearMap.smul_apply,hae,smul_zero]
  have hW : W ≤ B.orthogonal W := fun y hy x hx => hpair x hx y hy
  have hfin : finrank F V = 2*w := by
    have he := hdim
    rw [Module.natCard_eq_pow_finrank (K := F)] at he
    exact (Nat.pow_right_injective (Finite.one_lt_card (α := F))) he
  have hle := Submodule.finrank_mono hW
  rw [B.finrank_orthogonal hB W,hfin] at hle
  have hWdim : finrank F W ≤ w := by omega
  let f : E → F × W := fun x => (c x,⟨v x,Submodule.subset_span ⟨x,rfl⟩⟩)
  have hf : Function.Injective f := by
    intro x y he
    apply hi
    exact Prod.ext (congrArg (fun p : F × W => p.1) he) (congrArg (fun p : F × W => (p.2 : V)) he)
  calc
    Nat.card E ≤ Nat.card (F × W) := Nat.card_le_card_of_injective f hf
    _ = Nat.card F * Nat.card F ^ finrank F W := by
      rw [Nat.card_prod,Module.natCard_eq_pow_finrank (K := F) (V := W)]
    _ ≤ Nat.card F * Nat.card F^w := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (Nat.card_pos (α := F)) hWdim)
    _ = Nat.card F^(w+1) := (pow_succ' _ _).symm

open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
private def g2Form (F : Type*) [Field F] : LinearMap.BilinForm F (Fin 4 → F) where
  toFun v := {
    toFun := fun w => v 0*w 3 + v 3*w 0 + v 1*w 2 + v 2*w 1
    map_add' := by intros; simp only [Pi.add_apply]; ring
    map_smul' := by intros; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
  map_add' := by intros; apply LinearMap.ext; intro w; simp only [Pi.add_apply,LinearMap.add_apply,LinearMap.coe_mk,AddHom.coe_mk]; ring
  map_smul' := by intros; apply LinearMap.ext; intro w; simp only [Pi.smul_apply,LinearMap.smul_apply,smul_eq_mul,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk]; ring

private theorem g2Form_nondegenerate (F : Type*) [Field F] : (g2Form F).Nondegenerate := by
  constructor
  · intro v h
    have h0 := h ![0,0,0,1]
    have h1 := h ![0,0,1,0]
    have h2 := h ![0,1,0,0]
    have h3 := h ![1,0,0,0]
    simp [g2Form] at h0 h1 h2 h3
    ext i
    fin_cases i <;> assumption
  · intro v h
    have h0 := h ![0,0,0,1]
    have h1 := h ![0,0,1,0]
    have h2 := h ![0,1,0,0]
    have h3 := h ![1,0,0,0]
    simp [g2Form] at h0 h1 h2 h3
    ext i
    fin_cases i <;> assumption

private theorem g2_abelian_bound
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (E : Subgroup (radical₁ (F := F))) [IsMulCommutative E] :
    Nat.card E ≤ Nat.card F ^ 3 := by
  let t : E → (Fin 6 → F) := fun x => unipotentParameters x.val.val
  have ht (x : E) : unipotentProduct (t x)=x.val.val ∧ t x 5=0 := by
    obtain ⟨u,hu,he⟩ := x.val.property
    dsimp [t]
    rw [←he,unipotentParameters_product]
    exact ⟨rfl,hu⟩
  let v : E → (Fin 4 → F) := fun x => ![t x 1,t x 2,t x 3,t x 4]
  refine isotropic_coordinate_bound (g2Form F) (g2Form_nondegenerate F) (fun x => t x 0) v ?_ ?_ 2 ?_
  · intro x y he
    apply Subtype.ext
    apply Subtype.ext
    rw [←(ht x).1,←(ht y).1]
    congr 1
    have h0 := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    ext i
    fin_cases i
    · exact h0
    · exact congrFun hv 0
    · exact congrFun hv 1
    · exact congrFun hv 2
    · exact congrFun hv 3
    · exact (ht x).2.trans (ht y).2.symm
  · intro x y
    have hc : ⁅x.val.val,y.val.val⁆=1 := by
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg (fun a : E => a.val.val) (mul_comm x y))
    rw [←(ht x).1,←(ht y).1,fiveRoot_commutator _ _ (ht x).2 (ht y).2] at hc
    have hz := rootA_injective (hc.trans (rootA_zero (K := F)).symm)
    change t x 1*t y 4+t x 4*t y 1+t x 2*t y 3+t x 3*t y 2=0
    simp only [CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod] at hz
    convert hz using 1
    ring
  · simp [Nat.card_fun]

open _root_.Triality.Standard _root_.Triality.Standard.RadicalCoordinates.Centers

private theorem armsPairing_smul_left (P : Parameters) (a : fixedField P)
    (x y : ExtensionField P) : armsPairing P (a • x) y = a * armsPairing P x y := by
  change armsPairing P (a.val*x) y = a * armsPairing P x y
  apply Subtype.ext
  have ha : fieldFrobenius P a.val=a.val := a.property
  simp only [armsPairing_coe,map_mul,ha,Subfield.coe_mul]
  ring

private theorem armsPairing_smul_right (P : Parameters) (a : fixedField P)
    (x y : ExtensionField P) : armsPairing P x (a • y) = a * armsPairing P x y := by
  change armsPairing P x (a.val*y) = a * armsPairing P x y
  apply Subtype.ext
  have ha : fieldFrobenius P a.val=a.val := a.property
  simp only [armsPairing_coe,map_mul,ha,Subfield.coe_mul]
  ring

private abbrev TrialitySpace (P : Parameters) :=
  (Fin 2 → ExtensionField P) × (Fin 2 → fixedField P)

private def trialityForm (P : Parameters) : LinearMap.BilinForm (fixedField P) (TrialitySpace P) where
  toFun v := {
    toFun := fun w => v.2 1*w.2 0+w.2 1*v.2 0+
      armsPairing P (w.1 0) (v.1 1)+armsPairing P (v.1 0) (w.1 1)
    map_add' := by
      intros
      simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,armsPairing_add_left,armsPairing_add_right]
      ring
    map_smul' := by
      intros
      simp only [Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,armsPairing_smul_left,
        armsPairing_smul_right,smul_eq_mul,RingHom.id_apply]
      ring }
  map_add' := by
    intros
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,Prod.fst_add,Prod.snd_add,
      Pi.add_apply,armsPairing_add_left,armsPairing_add_right]
    ring
  map_smul' := by
    intros
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,Prod.smul_fst,Prod.smul_snd,
      Pi.smul_apply,armsPairing_smul_left,armsPairing_smul_right,smul_eq_mul,RingHom.id_apply]
    ring

private theorem trialityForm_nondegenerate (P : Parameters) (hp : P.prime=2) :
    (trialityForm P).Nondegenerate := by
  have hleft : (trialityForm P).SeparatingLeft := by
    intro v h
    have h0 := h (0,![0,1])
    have h1 := h (0,![1,0])
    have ha : v.1 0=0 := armsPairing_left_nondegenerate P hp _ (fun b => by
      have hh := h (![0,b],0)
      simpa [trialityForm] using hh)
    have hb : v.1 1=0 := armsPairing_right_nondegenerate P hp _ (fun b => by
      have hh := h (![b,0],0)
      simpa [trialityForm] using hh)
    simp [trialityForm] at h0 h1
    apply Prod.ext
    · funext i
      fin_cases i <;> assumption
    · funext i
      fin_cases i <;> assumption
  exact LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hleft

private theorem triality_abelian_bound (P : Parameters) (hp : P.prime=2)
    (E : Subgroup (armsSubgroup P)) [IsMulCommutative E] : Nat.card E ≤ P.q^5 := by
  let t : E → ArmsParameters P := fun x => (armsEquiv P hp).symm x.val
  have ht (x : E) : armsEquiv P hp (t x)=x.val := (armsEquiv P hp).apply_symm_apply _
  let v : E → TrialitySpace P := fun x => ((t x).1,![(t x).2 0,(t x).2 1])
  have hh : Nat.card E ≤ Nat.card (fixedField P)^5 := by
    refine isotropic_coordinate_bound (trialityForm P) (trialityForm_nondegenerate P hp)
      (fun x => (t x).2 2) v ?_ ?_ 4 ?_
    · intro x y he
      apply Subtype.ext
      rw [←ht x,←ht y]
      congr 1
      have hc := congrArg Prod.fst he
      have hv := congrArg Prod.snd he
      apply Prod.ext
      · exact congrArg (fun p : TrialitySpace P => p.1) hv
      · funext i
        fin_cases i
        · exact congrFun (congrArg (fun p : TrialitySpace P => p.2) hv) 0
        · exact congrFun (congrArg (fun p : TrialitySpace P => p.2) hv) 1
        · exact hc
    · intro x y
      have hc : ⁅x.val,y.val⁆=1 := by
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (congrArg Subtype.val (mul_comm x y))
      rw [←ht x,←ht y,armsEquiv_commutator P hp] at hc
      have hz := (armsEquiv_central_eq_one_iff P hp _).mp hc
      change (t x).2 1*(t y).2 0+(t y).2 1*(t x).2 0+
        armsPairing P ((t y).1 0) ((t x).1 1)+armsPairing P ((t x).1 0) ((t y).1 1)=0
      dsimp only [armsCommutator,armsCocycle] at hz
      convert hz using 1
      ring
    · rw [Nat.card_prod,Nat.card_fun,Nat.card_fun,card_extensionField,card_fixedField]
      norm_num
      ring
  simpa only [card_fixedField] using hh

open Theory.GroupTheory ChapterI.Section06To08
variable {G : Type*} [Group G]

private theorem core_square_in_factor_center
    {X : Type*} [Group X] [Finite X] {K : Subgroup G} (e : K ≃* X)
    (hfr : frattini (pCore 2 X) = center (pCore 2 X))
    (hc : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X) :
    ∀ x ∈ K.pCoreIn 2, x^2 ∈ (center K).map K.subtype := by
  rintro x ⟨a,ha,rfl⟩
  have hea : e a ∈ pCore 2 X := (pCore_map_iso 2 e) ▸ mem_map_of_mem e.toMonoidHom ha
  let b : pCore 2 X := ⟨e a,hea⟩
  let : Fact (IsPGroup 2 (pCore 2 X)) := ⟨pCore_isPGroup⟩
  have hb : b^2 ∈ center (pCore 2 X) := hfr ▸ pth_power_mem_frattini_of_isPGroup (p := 2) b
  have hbX : (e a)^2 ∈ center X := hc (mem_map_of_mem _ hb)
  refine ⟨a^2,mem_center_iff.mpr (fun k => ?_),rfl⟩
  apply e.injective
  simpa only [map_mul,map_pow] using mem_center_iff.mp hbX (e k)

private theorem core_abelian_model_bound
    {X R : Type*} [Group X] [Group R] [Finite X] [Finite R]
    {K : Subgroup G} (e : K ≃* X) (b : pCore 2 X ≃* R)
    {c : ℕ} (hbound : ∀ E : Subgroup R, IsMulCommutative E → Nat.card E ≤ c)
    (E : Subgroup G) [IsMulCommutative E] (hE : E ≤ K.pCoreIn 2) : Nat.card E ≤ c := by
  let a : K.pCoreIn 2 ≃* R :=
    ((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective).symm.trans
      (((e.subgroupMap (pCore 2 K)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))).trans b)
  let D := E.subgroupOf (K.pCoreIn 2)
  let d : D ≃* E := subgroupOfEquivOfLe hE
  let : IsMulCommutative D := ⟨⟨fun x y => d.injective (by
    simp only [map_mul]
    exact mul_comm _ _)⟩⟩
  have hD := hbound (D.map a.toMonoidHom) (Subgroup.map_isMulCommutative D a.toMonoidHom)
  rwa [card_map_of_injective a.injective,Nat.card_congr d.toEquiv] at hD

private theorem special_core_intersection
    {K : Subgroup G} (hTI : IsTISubgroup ((center K).map K.subtype))
    (hN : normalizer (((center K).map K.subtype : Subgroup G) : Set G)=normalizer (K : Set G))
    (hsq : ∀ x ∈ K.pCoreIn 2, x^2 ∈ (center K).map K.subtype)
    {c : ℕ} (hb : ∀ E : Subgroup G, IsMulCommutative E → E ≤ K.pCoreIn 2 → Nat.card E ≤ c)
    (g : G) (hg : g ∉ normalizer (K : Set G)) :
    let Q := K.pCoreIn 2
    IsElementaryAbelian 2 (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ∧
      Nat.card (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ c := by
  let Q := K.pCoreIn 2
  let Z := (center K).map K.subtype
  let D := Q ⊓ Q.map (MulAut.conj g).toMonoidHom
  have hd : Disjoint (Z.map (MulAut.conj g).toMonoidHom) Z := by
    rcases hTI.eq_or_disjoint_conjugate g with he | hd
    · exact (hg (hN ▸ mem_normalizer_iff_map_conj_eq.mpr he)).elim
    · exact hd
  have hs (x : D) : x^2=1 := by
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp hd
    · obtain ⟨y,hy,he⟩ := x.property.2
      change x.val^2 ∈ Z.map (MulAut.conj g).toMonoidHom
      rw [←he,←map_pow]
      exact mem_map_of_mem _ (hsq y hy)
    · exact hsq x x.property.1
  have hi (x : D) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
  let hc : IsMulCommutative D := ⟨⟨fun x y => by
    have hh := hi (x*y)
    rw [mul_inv_rev,hi x,hi y] at hh
    exact hh.symm⟩⟩
  exact ⟨{ toIsMulCommutative := hc
           exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs },hb D hc inf_le_left⟩

private theorem coordinate_centralizer_card
    {F V Q : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V]
    [Group Q] [Finite Q] (e : Q ≃ F × V) (B : LinearMap.BilinForm F V)
    (hc : ∀ x y : Q, x*y=y*x ↔ B (e x).2 (e y).2=0)
    (d : ℕ) (hd : Nat.card V = Nat.card F^d) (x : Q) (hx : x ∉ center Q) :
    Nat.card (centralizer ({x} : Set Q)) = Nat.card F^d := by
  let f := B (e x).2
  have hf : f ≠ 0 := by
    intro he
    apply hx
    apply mem_center_iff.mpr
    intro y
    exact ((hc x y).mpr (by change f (e y).2=0; rw [he]; rfl)).symm
  let a : centralizer ({x} : Set Q) → F × LinearMap.ker f :=
    fun y => ((e y.val).1,⟨(e y.val).2,(hc x y.val).mp
      (mem_centralizer_singleton_iff.mp y.property).symm⟩)
  have ha : Function.Bijective a := by
    constructor
    · intro y z he
      apply Subtype.ext
      apply e.injective
      exact Prod.ext (congrArg (fun t : F × LinearMap.ker f => t.1) he)
        (congrArg (fun t : F × LinearMap.ker f => t.2.val) he)
    · rintro ⟨c,v⟩
      refine ⟨⟨e.symm (c,v.val),mem_centralizer_singleton_iff.mpr ?_⟩,?_⟩
      · apply Eq.symm
        apply (hc _ _).mpr
        simpa only [e.apply_symm_apply] using (show f v.val=0 from v.property)
      · apply Prod.ext
        · exact congrArg (fun t : F × V => t.1) (e.apply_symm_apply (c,v.val))
        · apply Subtype.ext
          exact congrArg Prod.snd (e.apply_symm_apply (c,v.val))
  have hv : finrank F V=d := by
    rw [Module.natCard_eq_pow_finrank (K := F)] at hd
    exact Nat.pow_right_injective (Finite.one_lt_card (α := F)) hd
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [hv] at hk
  rw [Nat.card_congr (Equiv.ofBijective a ha),Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker f),←pow_succ',hk]

private def g2Coordinates {F : Type*} [Field F] :
    radical₁ (F := F) ≃ F × (Fin 4 → F) where
  toFun x := (unipotentParameters x.val 0,
    ![unipotentParameters x.val 1,unipotentParameters x.val 2,
      unipotentParameters x.val 3,unipotentParameters x.val 4])
  invFun v := ⟨unipotentProduct ![v.1,v.2 0,v.2 1,v.2 2,v.2 3,0],⟨_,rfl,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨t,ht,he⟩ := x.property
    change unipotentProduct ![unipotentParameters x.val 0,unipotentParameters x.val 1,
      unipotentParameters x.val 2,unipotentParameters x.val 3,unipotentParameters x.val 4,0]=x.val
    rw [←he,unipotentParameters_product]
    congr 1
    funext i
    fin_cases i <;> simp [ht]
  right_inv v := by
    simp only [unipotentParameters_product]
    refine Prod.ext ?_ ?_
    · rfl
    · funext i
      fin_cases i <;> rfl

private theorem g2Coordinates_commute {F : Type*} [Field F] [CharP F 2]
    (x y : radical₁ (F := F)) :
    x*y=y*x ↔ g2Form F (g2Coordinates x).2 (g2Coordinates y).2=0 := by
  obtain ⟨t,ht,he⟩ := x.property
  obtain ⟨u,hu,huv⟩ := y.property
  have hh : ⁅x.val,y.val⁆=rootA (g2Form F (g2Coordinates x).2 (g2Coordinates y).2) := by
    rw [←he,←huv,fiveRoot_commutator t u ht hu]
    congr 1
    change _ = g2Form F
      ![unipotentParameters x.val 1,unipotentParameters x.val 2,unipotentParameters x.val 3,unipotentParameters x.val 4]
      ![unipotentParameters y.val 1,unipotentParameters y.val 2,unipotentParameters y.val 3,unipotentParameters y.val 4]
    rw [←he,←huv,unipotentParameters_product,unipotentParameters_product]
    simp only [CharTwo.neg_eq,CharTwo.sub_eq_add,CharTwo.ofNat_eq_mod]
    change _ = t 1*u 4+t 4*u 1+t 2*u 3+t 3*u 2
    ring
  constructor
  · intro hc
    apply rootA_injective
    rw [←hh,rootA_zero]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val hc)
  · intro hc
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [hh,hc,rootA_zero]

private theorem g2_point_centralizer_card {F : Type*} [Field F] [Finite F] [CharP F 2]
    (x : radical₁ (F := F)) (hx : x ∉ center (radical₁ (F := F))) :
    Nat.card (centralizer ({x} : Set (radical₁ (F := F))))=Nat.card F^4 :=
  coordinate_centralizer_card g2Coordinates (g2Form F) g2Coordinates_commute 4
    (by simp [Nat.card_fun]) x hx

private def trialityCoordinates (P : Parameters) (hp : P.prime=2) :
    armsSubgroup P ≃ fixedField P × TrialitySpace P :=
  (armsEquiv P hp).symm.trans {
    toFun := fun v => (v.2 2,v.1,![v.2 0,v.2 1])
    invFun := fun v => (v.2.1,![v.2.2 0,v.2.2 1,v.1])
    left_inv := by
      intro v
      refine Prod.ext ?_ ?_
      · rfl
      · funext i
        fin_cases i <;> rfl
    right_inv := by
      intro v
      refine Prod.ext ?_ ?_
      · rfl
      · refine Prod.ext ?_ ?_
        · rfl
        · funext i
          fin_cases i <;> rfl }

private theorem trialityCoordinates_commute (P : Parameters) (hp : P.prime=2)
    (x y : armsSubgroup P) :
    x*y=y*x ↔ trialityForm P (trialityCoordinates P hp x).2
      (trialityCoordinates P hp y).2=0 := by
  obtain ⟨v,rfl⟩ := (armsEquiv P hp).surjective x
  obtain ⟨w,rfl⟩ := (armsEquiv P hp).surjective y
  rw [←commutatorElement_eq_one_iff_mul_comm,armsEquiv_commutator P hp,
    armsEquiv_central_eq_one_iff P hp]
  have hh : armsCommutator P v w = trialityForm P
      (trialityCoordinates P hp (armsEquiv P hp v)).2
      (trialityCoordinates P hp (armsEquiv P hp w)).2 := by
    simp only [trialityCoordinates,Equiv.trans_apply,Equiv.symm_apply_apply]
    change armsCommutator P v w =
      v.2 1*w.2 0+w.2 1*v.2 0+armsPairing P (w.1 0) (v.1 1)+armsPairing P (v.1 0) (w.1 1)
    dsimp only [armsCommutator,armsCocycle]
    ring
  rw [hh]

private theorem triality_point_centralizer_card (P : Parameters) (hp : P.prime=2)
    (x : armsSubgroup P) (hx : x ∉ center (armsSubgroup P)) :
    Nat.card (centralizer ({x} : Set (armsSubgroup P)))=P.q^8 := by
  have hc := coordinate_centralizer_card (trialityCoordinates P hp) (trialityForm P)
    (trialityCoordinates_commute P hp) 8 (by
      rw [Nat.card_prod,Nat.card_fun,Nat.card_fun,card_extensionField,card_fixedField]
      norm_num
      ring) x hx
  simpa only [card_fixedField] using hc

open CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

private theorem ti_core_centralizer_eq_point
    (Q Z : Subgroup G) (hTI : IsTISubgroup Z) (hZQ : Z ≤ Q)
    (hd : Disjoint Z ((center Q).map Q.subtype))
    (hclass : commutator Q ≤ center Q) (z : G) (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Q ⊓ centralizer (Z : Set G) = Q ⊓ centralizer ({z} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left Q (centralizer_le (Set.singleton_subset_iff.mpr hz))
  · rintro x ⟨hxQ,hxz⟩
    refine ⟨hxQ,mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hn := hTI.centralizer_le_normalizer hz hz1 hxz
    have hcy : ⁅x,y⁆ ∈ Z := by
      exact Z.mul_mem ((mem_normalizer_iff.mp hn y).mp hy) (Z.inv_mem hy)
    have hcQ : ⁅(⟨x,hxQ⟩ : Q),⟨y,hZQ hy⟩⁆ ∈ center Q :=
      hclass (commutator_mem_commutator (mem_top _) (mem_top _))
    have hcyQ : ⁅x,y⁆ ∈ (center Q).map Q.subtype := mem_map_of_mem _ hcQ
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.disjoint_def.mp hd hcy hcyQ)).symm

private def coreEquiv {X : Type*} [Group X] (K : Subgroup G) (e : K ≃* X) :
    K.pCoreIn 2 ≃* pCore 2 X :=
  ((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective).symm.trans
    ((e.subgroupMap (pCore 2 K)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e)))

private theorem core_center_le_factor_center
    {X : Type*} [Group X] {K : Subgroup G} (e : K ≃* X)
    (hc : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X) :
    (center (K.pCoreIn 2)).map (K.pCoreIn 2).subtype ≤ (center K).map K.subtype := by
  have hK : (center (pCore 2 K)).map (pCore 2 K).subtype ≤ center K := by
    let c := (e.symm.subgroupMap (pCore 2 X)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 e.symm))
    rw [←center_map_equiv c,Subgroup.map_map,←center_map_equiv e.symm]
    change (center (pCore 2 X)).map (e.symm.toMonoidHom.comp (pCore 2 X).subtype) ≤ _
    rw [←Subgroup.map_map]
    exact map_mono hc
  let c := (pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective
  change (center ((pCore 2 K).map K.subtype)).map ((pCore 2 K).map K.subtype).subtype ≤ _
  rw [←center_map_equiv c,Subgroup.map_map]
  change (center (pCore 2 K)).map (K.subtype.comp (pCore 2 K).subtype) ≤ _
  rw [←Subgroup.map_map]
  exact map_mono hK

private theorem conjugate_core_center_le
    {Q Z : Subgroup G} (hc : (center Q).map Q.subtype ≤ Z) (g : G) :
    (center (Q.map (MulAut.conj g).toMonoidHom)).map
        (Q.map (MulAut.conj g).toMonoidHom).subtype ≤ Z.map (MulAut.conj g).toMonoidHom := by
  let c := Q.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [←center_map_equiv c,Subgroup.map_map]
  change (center Q).map ((MulAut.conj g).toMonoidHom.comp Q.subtype) ≤ _
  rw [←Subgroup.map_map]
  exact map_mono hc

private theorem class_two_of_equiv {Q X : Type*} [Group Q] [Group X] (e : Q ≃* X)
    (hc : commutator X ≤ center X) : commutator Q ≤ center Q := by
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [center_map_equiv,map_commutator_eq,e.toMonoidHom.range_eq_top_of_surjective e.surjective]
  exact hc

private theorem point_centralizer_card_transport
    {X : Type*} [Group X] (Q : Subgroup G) (e : Q ≃* X) {c : ℕ}
    (hb : ∀ x : X, x ∉ center X → Nat.card (centralizer ({x} : Set X))=c)
    (x : G) (hx : x ∈ Q) (hz : x ∉ (center Q).map Q.subtype) :
    Nat.card (Q ⊓ centralizer ({x} : Set G) : Subgroup G)=c := by
  let a : Q := ⟨x,hx⟩
  have ha : e a ∉ center X := by
    intro he
    apply hz
    refine ⟨a,mem_center_iff.mpr ?_,rfl⟩
    intro q
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp he (e q)
  let f : (Q ⊓ centralizer ({x} : Set G) : Subgroup G) →
      centralizer ({e a} : Set X) := fun y => ⟨e ⟨y.val,y.property.1⟩,
    mem_centralizer_singleton_iff.mpr (by
      rw [←map_mul,←map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp y.property.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro y z he
      exact Subtype.ext (congrArg (fun q : Q => q.val) (e.injective (congrArg Subtype.val he)))
    · intro y
      let b := e.symm y.val
      have hb : b.val ∈ centralizer ({x} : Set G) := by
        apply mem_centralizer_singleton_iff.mpr
        have hh : b*a=a*b := e.injective (by
          simpa only [map_mul,b,e.apply_symm_apply] using
            mem_centralizer_singleton_iff.mp y.property)
        exact congrArg Subtype.val hh
      exact ⟨⟨b.val,b.property,hb⟩,Subtype.ext (e.apply_symm_apply y.val)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).trans (hb (e a) ha)

private theorem factor_center_nontrivial
    {X R : Type*} [Group X] [Group R] [Finite R] {K : Subgroup G}
    (e : K ≃* X) (b : pCore 2 X ≃* R)
    (hcenter : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X)
    (hc : 1 < Nat.card (center R)) :
    ∃ z ∈ (center K).map K.subtype, z ≠ 1 := by
  let c := (coreEquiv K e).trans b
  let : Nontrivial (center R) := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨r,hr⟩ := exists_ne (1 : center R)
  let x := (centerCongr c).symm r
  refine ⟨x.val.val,core_center_le_factor_center e hcenter (mem_map_of_mem _ x.property),?_⟩
  intro hh
  apply hr
  exact (centerCongr c).symm.map_eq_one_iff.mp
    (show x=1 from Subtype.ext (Subtype.ext hh))

private theorem root_centralizer_card
    {X R : Type*} [Group X] [Group R] {K : Subgroup G}
    (e : K ≃* X) (b : pCore 2 X ≃* R)
    (hcenter : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X)
    (hclass : commutator R ≤ center R)
    {c : ℕ} (hcard : ∀ x : R, x ∉ center R → Nat.card (centralizer ({x} : Set R))=c)
    (hTI : IsTISubgroup ((center K).map K.subtype))
    (hN : normalizer (((center K).map K.subtype : Subgroup G) : Set G)=normalizer (K : Set G))
    (hz : ∃ z ∈ (center K).map K.subtype, z ≠ 1)
    (g : G) (hg : g ∉ normalizer (K : Set G))
    (hZQ : (center K).map K.subtype ≤ (K.pCoreIn 2).map (MulAut.conj g).toMonoidHom) :
    Nat.card ((K.pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center K).map K.subtype : Subgroup G) : Set G) : Subgroup G)=c := by
  let Z := (center K).map K.subtype
  let Q := (K.pCoreIn 2).map (MulAut.conj g).toMonoidHom
  have hd : Disjoint Z (Z.map (MulAut.conj g).toMonoidHom) := by
    rcases hTI.eq_or_disjoint_conjugate g with he | hd
    · exact (hg (hN ▸ mem_normalizer_iff_map_conj_eq.mpr he)).elim
    · exact hd.symm
  have hcenterQ : (center Q).map Q.subtype ≤ Z.map (MulAut.conj g).toMonoidHom :=
    conjugate_core_center_le (core_center_le_factor_center e hcenter) g
  let a : Q ≃* R := ((K.pCoreIn 2).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans ((coreEquiv K e).trans b)
  obtain ⟨z,hz,hz1⟩ := hz
  rw [ti_core_centralizer_eq_point Q Z hTI hZQ (hd.mono_right hcenterQ)
    (class_two_of_equiv a hclass) z hz hz1]
  exact point_centralizer_card_transport Q a hcard z (hZQ hz)
    (fun hc => hz1 (Subgroup.disjoint_def.mp hd hz (hcenterQ hc)))

private theorem special_core_saturation [Finite G]
    (S Q R : Subgroup G) (q w : ℕ) (hq : 0<q)
    (hQ : Q ≤ S) (hR : R ≤ S) (hn : S ≤ normalizer (Q : Set G))
    (hSc : Nat.card S=q^(3*w)) (hQc : Nat.card Q=q^(2*w+1))
    (hRc : Nat.card R=q^(2*w)) (hIc : Nat.card (Q ⊓ R : Subgroup G) ≤ q^(w+1)) :
    S=Q ⊔ R := by
  apply (Subgroup.eq_of_le_of_card_ge (sup_le hQ hR) ?_).symm
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q R (hR.trans hn)
  have he : q^(w+1)*Nat.card S=Nat.card Q*Nat.card R := by
    rw [hSc,hQc,hRc,←pow_add,←pow_add]
    congr 1
    omega
  apply Nat.le_of_mul_le_mul_left (c := q^(w+1)) ?_ (pow_pos hq _)
  rw [he,hprod]
  exact Nat.mul_le_mul_right _ hIc

end SpecialIntersection

open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The F.4.35 intersection calculation for the actual G₂ right core. Distinct
ambient root centers force exponent two, and the concrete symplectic form
bounds the entire intersection by q³, for q = 2^n. -/
theorem Preparation.g2_special_core_intersection
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (g : G) (hg : g ∉ normalizer (residual H : Set G)) :
    let Q := (residual H).pCoreIn 2
    IsElementaryAbelian 2 (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ∧
      Nat.card (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ (2^n)^3 := by
  have hf := d.g2_right_center_fusion h hH hp F he
  have hs := d.g2_local_structure h hH.1.1.2 hp F he
  obtain ⟨a⟩ := hs.2.2.1
  apply SpecialIntersection.special_core_intersection hf.2.1 hf.2.2
    (SpecialIntersection.core_square_in_factor_center a
      Atlas.G2.LieParabolicSetup.local₁_pCore_special.2.2.2.1
      Atlas.G2.LieParabolicSetup.local₁_core_center_le_center) ?_ g hg
  intro E hE hEQ
  let := hE
  apply SpecialIntersection.core_abelian_model_bound a
    Atlas.G2.LieParabolicSetup.local₁CoreEquivRadical ?_ E hEQ
  intro U hU
  let := hU
  simpa only [hs.1] using SpecialIntersection.g2_abelian_bound U

/-- The same literal special-core intersection in the genuine triality row
has order at most q⁵. The cubic trace commutator form supplies the bound;
no binary extraspecial hypothesis is used. -/
theorem Preparation.triality_special_core_intersection
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (g : G) (hg : g ∉ normalizer (residual H : Set G)) :
    let Q := (residual H).pCoreIn 2
    IsElementaryAbelian 2 (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ∧
      Nat.card (Q ⊓ Q.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ (2^n)^5 := by
  have hf := d.triality_right_center_fusion h hH hp m hm he
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hH.1.1.2 hp
      (_root_.Triality.Standard.binaryParameters m hm) rfl he).elim
  obtain ⟨e⟩ := he
  have hs := d.triality_local_structure h hH.1.1.2 hp m hm e
  obtain ⟨a⟩ := hs.2.2.2.1
  let P := _root_.Triality.Standard.binaryParameters m hm
  open _root_.Triality.Standard.Parabolics _root_.Triality.Standard.RadicalCoordinates in
  apply SpecialIntersection.special_core_intersection hf.2.1 hf.2.2
    (SpecialIntersection.core_square_in_factor_center a
      (localFactor_arms_twoCore_center_eq_frattini P rfl).symm
      (arms_core_center_le_center P rfl)) ?_ g hg
  intro E hE hEQ
  let := hE
  open _root_.Triality.Standard.Parabolics in
  apply SpecialIntersection.core_abelian_model_bound a
    ((localFactorTwoCoreEquivRadical P rfl .arms).trans
      (MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P rfl .arms))) ?_ E hEQ
  intro U hU
  let := hU
  simpa only [P,_root_.Triality.Standard.binaryParameters_q,hs.1] using
    SpecialIntersection.triality_abelian_bound P rfl U

namespace SpecialIntersection

private theorem source_sylow_card
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {T : Sylow 2 G} {L H A B K : Subgroup G}
    (d : Preparation T L H A B K) (hS : sourceS L H ≤ K)
    (e : K ≃* X) (P : Sylow 2 X) : Nat.card (sourceS L H)=Nat.card P := by
  obtain ⟨U,hU⟩ := (show ∃ U : Sylow 2 K,
    (U : Subgroup K).map K.subtype=sourceS L H ⊓ K from d.sylow 1)
  rw [inf_eq_left.mpr hS] at hU
  let U' : Sylow 2 X := U.mapSurjective (f := e.toMonoidHom) e.surjective
  calc
    Nat.card (sourceS L H) = Nat.card U := by
      rw [←hU,card_map_of_injective K.subtype_injective]
    _ = Nat.card U' := (card_map_of_injective e.injective).symm
    _ = Nat.card P := Nat.card_congr (U'.equiv P).toEquiv

private theorem source_core_le_sylow
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B K : Subgroup G}
    (d : Preparation T L H A B K) (hS : sourceS L H ≤ K) :
    K.pCoreIn 2 ≤ sourceS L H := by
  obtain ⟨U,hU⟩ := (show ∃ U : Sylow 2 K,
    (U : Subgroup K).map K.subtype=sourceS L H ⊓ K from d.sylow 1)
  rw [inf_eq_left.mpr hS] at hU
  exact (pCoreIn_le_sylow K U).trans_eq hU

end SpecialIntersection

/-- Exact centralizer counts for the actual G₂ core. The whole-root count
requires precisely the placement Z(K) ≤ Q^g made in F.4.35; the point count
is unconditional for every noncentral element of Q. -/
theorem Preparation.g2_special_core_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    (∀ x ∈ Q, x ∉ Z → Nat.card (Q ⊓ centralizer ({x} : Set G) : Subgroup G)=(2^n)^4) ∧
    (∀ g : G, g ∉ normalizer (residual H : Set G) →
      Z ≤ Q.map (MulAut.conj g).toMonoidHom →
      Nat.card (Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) : Subgroup G)=(2^n)^4) := by
  have hs := d.g2_local_structure h hH.1.1.2 hp F he
  have hf := d.g2_right_center_fusion h hH hp F he
  obtain ⟨a⟩ := hs.2.2.1
  let b := Atlas.G2.LieParabolicSetup.local₁CoreEquivRadical (F := F)
  have hc := Atlas.G2.LieParabolicSetup.local₁_core_center_le_center (F := F)
  have hb (x : Atlas.G2.LieParabolicSetup.radical₁ (F := F)) (hx : x ∉ center _) :
      Nat.card (centralizer ({x} : Set _))=(2^n)^4 := by
    simpa only [hs.1] using SpecialIntersection.g2_point_centralizer_card x hx
  refine ⟨?_,?_⟩
  · intro x hx hxZ
    exact SpecialIntersection.point_centralizer_card_transport _
      ((SpecialIntersection.coreEquiv _ a).trans b) hb x hx
      (fun hxC => hxZ (SpecialIntersection.core_center_le_factor_center a hc hxC))
  · have hz := SpecialIntersection.factor_center_nontrivial a b hc (by
      rw [Nat.card_congr (Atlas.G2.LieParabolicSetup.centerEquivHighestRoot
        (Atlas.G2.LieParabolicSetup.radical₁ (F := F)) le_rfl
        (Atlas.G2.LieParabolicSetup.fiveRootSubgroup_le_unipotent _ _)).toEquiv]
      exact Finite.one_lt_card (α := F))
    exact SpecialIntersection.root_centralizer_card a b hc
      (le_of_eq Atlas.G2.LieParabolicSetup.radical₁_commutator_eq_center) hb hf.2.1 hf.2.2 hz

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
  _root_.Triality.Standard.RadicalCoordinates _root_.Triality.Standard.RadicalCoordinates.Centers

/-- The genuine triality core has point and placed whole-root centralizers of order q^8. -/
theorem Preparation.triality_special_core_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    (∀ x ∈ Q, x ∉ Z → Nat.card (Q ⊓ centralizer ({x} : Set G) : Subgroup G)=(2^n)^8) ∧
    (∀ g : G, g ∉ normalizer (residual H : Set G) →
      Z ≤ Q.map (MulAut.conj g).toMonoidHom →
      Nat.card (Q.map (MulAut.conj g).toMonoidHom ⊓ centralizer (Z : Set G) : Subgroup G)=(2^n)^8) := by
  have hf := d.triality_right_center_fusion h hH hp m hm he
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hH.1.1.2 hp
      (_root_.Triality.Standard.binaryParameters m hm) rfl he).elim
  obtain ⟨e⟩ := he
  have hs := d.triality_local_structure h hH.1.1.2 hp m hm e
  obtain ⟨a⟩ := hs.2.2.2.1
  let P := _root_.Triality.Standard.binaryParameters m hm
  let b := (localFactorTwoCoreEquivRadical P rfl .arms).trans
    (MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P rfl .arms))
  have hc := arms_core_center_le_center P rfl
  have hb (x : armsSubgroup P) (hx : x ∉ center _) :
      Nat.card (centralizer ({x} : Set _))=(2^n)^8 := by
    simpa only [P,binaryParameters_q,hs.1] using
      SpecialIntersection.triality_point_centralizer_card P rfl x hx
  refine ⟨?_,?_⟩
  · intro x hx hxZ
    exact SpecialIntersection.point_centralizer_card_transport _
      ((SpecialIntersection.coreEquiv _ a).trans b) hb x hx
      (fun hxC => hxZ (SpecialIntersection.core_center_le_factor_center a hc hxC))
  · have hz := SpecialIntersection.factor_center_nontrivial a b hc (by
      rw [card_center_arms P rfl]
      exact Nat.one_lt_pow (by omega : m ≠ 0) (by decide : 1 < (2 : ℕ)))
    exact SpecialIntersection.root_centralizer_card a b hc
      (le_of_eq (center_arms_eq_commutator P rfl).symm) hb hf.2.1 hf.2.2 hz

namespace SpecialIntersection

private theorem source_index_of_orders
    {G : Type*} [Group G] (Q S : Subgroup G) (hQ : Q ≤ S)
    (q w : ℕ) (hq : 0<q) (hw : 0<w)
    (hQc : Nat.card Q=q^(2*w+1)) (hSc : Nat.card S=q^(3*w)) :
    Q.relIndex S=q^(w-1) := by
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) Q S bot_le hQ
  rw [relIndex_bot_left,relIndex_bot_left,hQc,hSc] at hc
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hq (2*w+1))
  rw [hc,←pow_add]
  congr 1
  omega

end SpecialIntersection

/-- The exact original Sylow/core index and the product conclusion of F.4.35
for the G₂ comparison. Only the two source placements remain explicit. -/
theorem Preparation.g2_special_core_saturation
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))

    (g : G) (hg : g ∉ normalizer (residual H : Set G))
    (hZQ : (center (residual H)).map (residual H).subtype ≤
      ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom)
    (hRS : ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H) :
    let Q := (residual H).pCoreIn 2
    Q.relIndex (sourceS L H)=(2^n)^1 ∧
    sourceS L H = Q ⊔ (Q.map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) := by
  have hs := d.g2_local_structure h hH.1.1.2 hp F he
  have hi := d.g2_special_core_intersection h hH hp F he g hg
  have hc := (d.g2_special_core_centralizers h hH hp F he).2 g hg hZQ
  obtain ⟨a⟩ := hs.2.2.1
  have hSK : sourceS L H ≤ residual H := hs.2.2.2.2 1
  have hSc : Nat.card (sourceS L H)=(2^n)^6 := by
    have hh := SpecialIntersection.source_sylow_card d hSK a
      ((Atlas.G2.LieParabolicSetup.sylow (F := F)).subtype
        Atlas.G2.LieParabolicSetup.sylow_le_local₁)
    change Nat.card (sourceS L H)=Nat.card
      ((Atlas.G2.LieParabolicSetup.sylow (F := F) : Subgroup (Atlas.G2.Model F)).subgroupOf
        Atlas.G2.LieParabolicSetup.local₁) at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe Atlas.G2.LieParabolicSetup.sylow_le_local₁).toEquiv] at hh
    change Nat.card (sourceS L H)=Nat.card (Atlas.G2.unipotent (K := F)) at hh
    rw [Atlas.G2.card_unipotent,hs.1] at hh
    exact hh
  have hQc : Nat.card ((residual H).pCoreIn 2)=(2^n)^5 := by
    rw [Nat.card_congr (SpecialIntersection.coreEquiv _ a).toEquiv,
      Atlas.G2.LieParabolicSetup.local₁_pCore_special.2.2.2.2.2.1,hs.1]
  have hQS := SpecialIntersection.source_core_le_sylow d hSK
  have hnQ : sourceS L H ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
    hSK.trans ((residual H).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (residual H) (pCore 2 (residual H))))
  refine ⟨SpecialIntersection.source_index_of_orders _ _ hQS (2^n) 2
    (by positivity) (by decide) hQc hSc,?_⟩
  apply SpecialIntersection.special_core_saturation _ _ _ (2^n) 2 (by positivity)
    hQS hRS hnQ hSc hQc hc
  exact (card_le_of_le (show (residual H).pCoreIn 2 ⊓
    (((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) ≤
    (residual H).pCoreIn 2 ⊓ ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom from
      inf_le_inf_left _ inf_le_left)).trans hi.2

/-- The exact original Sylow/core index and the product conclusion of F.4.35
for the triality comparison. Only the two source placements remain explicit. -/
theorem Preparation.triality_special_core_saturation
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse))

    (g : G) (hg : g ∉ normalizer (residual H : Set G))
    (hZQ : (center (residual H)).map (residual H).subtype ≤
      ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom)
    (hRS : ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ sourceS L H) :
    let Q := (residual H).pCoreIn 2
    Q.relIndex (sourceS L H)=(2^n)^3 ∧
    sourceS L H = Q ⊔ (Q.map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) := by
  have hi := d.triality_special_core_intersection h hH hp m hm he g hg
  have hc := (d.triality_special_core_centralizers h hH hp m hm he).2 g hg hZQ
  have hSK : sourceS L H ≤ residual H := d.triality_sourceS_le_factors h hH.1.1.2 hp m hm he 1
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hH.1.1.2 hp
      (_root_.Triality.Standard.binaryParameters m hm) rfl he).elim
  obtain ⟨e⟩ := he
  have hs := d.triality_local_structure h hH.1.1.2 hp m hm e
  obtain ⟨a⟩ := hs.2.2.2.1
  let P := binaryParameters m hm
  have hSc : Nat.card (sourceS L H)=(2^n)^12 := by
    have hh := SpecialIntersection.source_sylow_card d hSK a
      ((ChapterF.GreenBook.LieModels.Triality.sylow P rfl).subtype
        (ChapterF.GreenBook.LieModels.Triality.sylow_le_localFactor P rfl .arms))
    change Nat.card (sourceS L H)=Nat.card
      ((ChapterF.GreenBook.LieModels.Triality.sylow P rfl : Subgroup (Carrier P)).subgroupOf
        (localFactor P .arms)) at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (ChapterF.GreenBook.LieModels.Triality.sylow_le_localFactor P rfl .arms)).toEquiv] at hh
    change Nat.card (sourceS L H)=Nat.card (unipotent P) at hh
    rw [card_unipotent_binary P rfl] at hh
    simpa only [P,binaryParameters_q,hs.1] using hh
  have hQc : Nat.card ((residual H).pCoreIn 2)=(2^n)^9 := by
    rw [Nat.card_congr (SpecialIntersection.coreEquiv _ a).toEquiv,
      localFactor_arms_twoCore_card P rfl]
    simp only [P,binaryParameters_q,hs.1]
  have hQS := SpecialIntersection.source_core_le_sylow d hSK
  have hnQ : sourceS L H ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
    hSK.trans ((residual H).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (residual H) (pCore 2 (residual H))))
  refine ⟨SpecialIntersection.source_index_of_orders _ _ hQS (2^n) 4
    (by positivity) (by decide) hQc hSc,?_⟩
  apply SpecialIntersection.special_core_saturation _ _ _ (2^n) 4 (by positivity)
    hQS hRS hnQ hSc hQc hc
  exact (card_le_of_le (show (residual H).pCoreIn 2 ⊓
    (((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G)) ≤
    (residual H).pCoreIn 2 ⊓ ((residual H).pCoreIn 2).map (MulAut.conj g).toMonoidHom from
      inf_le_inf_left _ inf_le_left)).trans hi.2


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
