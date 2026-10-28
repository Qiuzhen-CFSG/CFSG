module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition.Model
public import Theory.Representation.G2NaturalRootCentralizers
public import Theory.Representation.G2NaturalOffenders.SmallMoved

/-!
# Recognizing the full G₂ actor at parameter 2n

The containment calculation places an A_(2n) actor in a conjugate of the
concrete A-B-C group. If its binary subspace were proper, a nonzero binary
functional would vanish on it. Restricting scalar multiples in the A-B plane
produces a whole field line in that functional's kernel. The corresponding
actual long-root group then has relative corank below 2n in the actor.
Equality of fixed spaces contradicts the short-root fixed codimension.
This proves equality with the full group of order q³, for every field degree.

The field-line argument replaces the equivalent projective-line count in
the source. No projective group or numerical family tag is used.
The chosen-module application is ActorRecognition.Source.
Source: Aschbacher--Smith B.4.6(9), printed p.89, and 11.2.2(5), p.768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.ValueBound
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
open Atlas.G2 Atlas.G2.NaturalOffenders Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Finite F]

omit [CharP F 2] in
private theorem exists_direction (φ : (Fin 3 → F) →ₗ[ZMod 2] ZMod 2) :
    ∃ p : F × F, p ≠ 0 ∧ ∀ t : F, φ ![t*p.1,t*p.2,0] = 0 := by
  let j : (F × F) →ₗ[ZMod 2] Module.Dual (ZMod 2) F := {
    toFun p := {
      toFun t := φ ![t*p.1,t*p.2,0]
      map_add' t u := by
        rw [show ![(t+u)*p.1,(t+u)*p.2,0] = ![t*p.1,t*p.2,0] + ![u*p.1,u*p.2,0] by
          ext i; fin_cases i <;> simp [add_mul]]
        exact map_add φ _ _
      map_smul' t u := by
        rw [show ![(t • u)*p.1,(t • u)*p.2,0] = t • ![u*p.1,u*p.2,0] by
          ext i; fin_cases i <;> simp]
        exact map_smul φ _ _ }
    map_add' p q := by
      apply LinearMap.ext
      intro t
      change φ ![t*(p.1+q.1),t*(p.2+q.2),0] = _
      rw [show ![t*(p.1+q.1),t*(p.2+q.2),0] = ![t*p.1,t*p.2,0] + ![t*q.1,t*q.2,0] by
        ext i; fin_cases i <;> simp [mul_add],map_add]
      rfl
    map_smul' c p := by
      apply LinearMap.ext
      intro t
      change φ ![t*(c • p.1),t*(c • p.2),0] = _
      rw [show ![t*(c • p.1),t*(c • p.2),0] = c • ![t*p.1,t*p.2,0] by
        ext i; fin_cases i <;> simp,map_smul]
      rfl }
  have hj : j.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Subspace.dual_finrank_eq,Module.finrank_prod]
    have hp : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
    omega)
  obtain ⟨p,hp,hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hj
  refine ⟨p,hp0,?_⟩
  intro t
  exact congrArg (fun f : Module.Dual (ZMod 2) F => f t) hp

private theorem exists_root_in_kernel (φ : (Fin 3 → F) →ₗ[ZMod 2] ZMod 2) :
    ∃ g : Model F,
      (highestRoot.map (MulAut.conj g).toMonoidHom : Subgroup (Model F)) ≤
        ((φ.toAddMonoidHom.toMultiplicative).ker).map (EvenTwoRank.elementaryEmbedding F) := by
  obtain ⟨p,hp,hφ⟩ := exists_direction φ
  by_cases hb : p.2 = 0
  · have ha : p.1 ≠ 0 := by
      intro ha
      exact hp (Prod.ext ha hb)
    refine ⟨1,?_⟩
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd ![a.toAdd,0,0],?_,?_⟩
    · change φ ![a.toAdd,0,0] = 0
      simpa [hb,ha] using hφ (a.toAdd / p.1)
    · simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,
        unipotentProduct,highestRootHom]
  · refine ⟨rootE (p.1/p.2) * weylR,?_⟩
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd ![(p.1/p.2)*a.toAdd,a.toAdd,0],?_,?_⟩
    · change φ ![(p.1/p.2)*a.toAdd,a.toAdd,0] = 0
      convert hφ (a.toAdd/p.2) using 1
      congr 1
      ext i
      fin_cases i <;> simp [hb]
      ring
    · change EvenTwoRank.elementaryEmbedding F _ = MulAut.conj (rootE (p.1/p.2) * weylR) (rootA a.toAdd)
      rw [map_mul,MulAut.mul_apply]
      rw [show MulAut.conj weylR (rootA a.toAdd) = rootB a.toAdd from weylR_rootA _]
      rw [ShortRootProducts.rootE_conjugate_rootB]
      simp [EvenTwoRank.elementaryEmbedding,EvenTwoRank.elementaryParameters,unipotentProduct]

private theorem highest_fixedCodim {n : ℕ} (hc : Nat.card F = 2^n) :
    fixedCodim (binaryAction (F:=F)) highestRoot = 2*n := by
  have he : fixedSpace (binaryAction (F:=F)) highestRoot =
      (upperFour (F:=F)).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv
      exact (fixed_rootA_iff (1:F) one_ne_zero v).mp (hv ⟨rootA 1,⟨Multiplicative.ofAdd 1,rfl⟩⟩)
    · intro hv a
      obtain ⟨r,hr⟩ := a.property
      change Restricted.NaturalCoordinates.action F a.val v = v
      rw [←hr]
      change Restricted.NaturalCoordinates.action F (rootA r.toAdd) v = v
      have h4 : v 4 = 0 := hv.1
      have h5 : v 5 = 0 := hv.2
      ext i
      fin_cases i <;> simp [h4,h5]
  have h := fixedCodim_add_finrank (binaryAction (F:=F)) highestRoot
  rw [he,upperFour_binary_finrank hc,coordinates_binary_finrank hc] at h
  omega

private theorem family_contains_shortRoot {n k : ℕ} (hc : Nat.card F = 2^n) (hn : n<k)
    (A : Subgroup (Model F)) (hA : A ∈ fixedSpaceFamily (binaryAction (F:=F)) k) :
    ∃ b ∈ A, ShortRootProducts.IsShortRootElement b := by
  let := hA.2.1.2
  by_contra hs
  have hp : ∀ b ∈ A, b ≠ 1 → ShortRootProducts.IsLongRootElement b := by
    intro b hb hne
    rcases EvenInvolutionGeometry.involution_isRoot
      (elemPow_eq_one_of_isElementaryAbelian b hb) hne with ⟨g,r,hr,he⟩ | ⟨g,r,hr,he⟩
    · exact ⟨r,hr,g,he⟩
    · exact (hs ⟨b,hb,r,hr,g,he⟩).elim
  obtain ⟨g,hg⟩ := EvenInvolutionGeometry.PureLong.exists_map_le_longRootLocal A hA.2.1.2 hp
  exact not_family_of_le_longRootLocal hc hn _ hg
    (fixedSpaceFamily_conjugationInvariant _ _ A hA g)

/-- The maximal fixed-space parameter forces the whole q³ group; no
proper binary subgroup of that group retains parameter 2n. -/
theorem eq_elementary_of_le {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) (hA : A ∈ fixedSpaceFamily (binaryAction (F:=F)) (2*n))
    (hAE : A ≤ EvenTwoRank.elementary F) : A = EvenTwoRank.elementary F := by
  classical
  by_contra hne
  let e := EvenTwoRank.elementaryEmbedding F
  let P : Submodule (ZMod 2) (Fin 3 → F) := AddSubgroup.toZModSubmodule 2
    (AddSubgroup.toSubgroup.symm (A.comap e))
  have hP : P ≠ ⊤ := by
    intro hP
    apply hne
    apply le_antisymm hAE
    rintro _ ⟨v,rfl⟩
    have hv : v.toAdd ∈ P := hP.symm ▸ Submodule.mem_top
    exact hv
  obtain ⟨φ,hφ,hPφ⟩ := P.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hP)
  let H := (φ.toAddMonoidHom.toMultiplicative.ker).map e
  have hAH : A ≤ H := by
    intro a ha
    obtain ⟨v,rfl⟩ := hAE ha
    exact ⟨v,hPφ (show v.toAdd ∈ P from ha),rfl⟩
  have hHE : H ≤ EvenTwoRank.elementary F := map_le_range _ _
  have hHne : H ≠ EvenTwoRank.elementary F := by
    intro he
    have hk : φ.toAddMonoidHom.toMultiplicative.ker = ⊤ := by
      apply map_injective (EvenTwoRank.elementaryEmbedding_injective F)
      simpa only [H,e,EvenTwoRank.elementary,←MonoidHom.range_eq_map] using he
    apply hφ
    apply LinearMap.ext
    intro v
    have hv : Multiplicative.ofAdd v ∈ φ.toAddMonoidHom.toMultiplicative.ker := hk.symm ▸ mem_top _
    exact hv
  have hHcard : Nat.card H < Nat.card (EvenTwoRank.elementary F) := by
    apply lt_of_not_ge
    intro he
    exact hHne (eq_of_le_of_card_ge hHE he)
  obtain ⟨g,hg⟩ := exists_root_in_kernel φ
  let Z : Subgroup (Model F) := highestRoot.map (MulAut.conj g).toMonoidHom
  have hZH : Z ≤ H := hg
  have hZcard : Nat.card Z = 2^n := by
    rw [card_map_of_injective (MulAut.conj g).injective,card_highestRoot,hc]
  have hindex : Z.relIndex H < 2^(2*n) := by
    have hh := relIndex_mul_card_of_le hZH
    rw [hZcard] at hh
    rw [EvenTwoRank.elementary_card,hc,←pow_mul] at hHcard
    have he : 2^(2*n)*2^n = 2^(n*3) := by rw [←pow_add]; congr 1; omega
    apply (Nat.mul_lt_mul_right (Nat.two_pow_pos n)).mp
    rw [hh,he]
    exact hHcard
  have hfix := hA.2.2 (A ⊓ Z) inf_le_left (by
    rw [inf_relIndex_left]
    apply Nat.log_lt_of_lt_pow' (by omega : 2*n ≠ 0)
    exact (relIndex_le_of_le_right hAH (Z.subgroupOf H).index_ne_zero_of_finite).trans_lt hindex)
  have hZA : fixedSpace (binaryAction (F:=F)) Z ≤ fixedSpace (binaryAction (F:=F)) A := by
    rw [hfix]
    exact BinaryOffender.fixedSpace_antitone _ inf_le_right
  have hdim := Submodule.finrank_mono hZA
  have hdimA := fixedCodim_add_finrank (binaryAction (F:=F)) A
  have hdimZ := fixedCodim_add_finrank (binaryAction (F:=F)) Z
  have hZcost : fixedCodim (binaryAction (F:=F)) Z = 2*n := by
    rw [fixedCodim_map_conj]
    exact highest_fixedCodim hc
  obtain ⟨b,hb,r,hr,x,hx⟩ := family_contains_shortRoot hc (by omega : n<2*n) A hA
  have hbfix := BinaryOffender.fixedSpace_antitone (binaryAction (F:=F)) (zpowers_le.mpr hb)
  have hbDim := Submodule.finrank_mono hbfix
  have hbEq := fixedCodim_add_finrank (binaryAction (F:=F)) (zpowers b)
  have hbcost : fixedCodim (binaryAction (F:=F)) (zpowers b) = 3*n := by
    rw [hx]
    change fixedCodim (binaryAction (F:=F)) (zpowers ((MulAut.conj x).toMonoidHom (rootC r))) = _
    rw [←MonoidHom.map_zpowers,fixedCodim_map_conj]
    exact fixedCodim_rootC hc r hr
  omega

/-- The full A_(2n) classification in the literal even G₂ natural module. -/
theorem family_eq_conjugate_elementary {n : ℕ} (hc : Nat.card F = 2^n) (hn : 0<n)
    (A : Subgroup (Model F)) (hA : A ∈ fixedSpaceFamily (binaryAction (F:=F)) (2*n)) :
    ∃ g : Model F, A = (EvenTwoRank.elementary F).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := family_le_conjugate_elementary hc (by omega : n<2*n) A hA
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : B ∈ fixedSpaceFamily (binaryAction (F:=F)) (2*n) :=
    fixedSpaceFamily_conjugationInvariant _ _ A hA g⁻¹
  have hBE : B ≤ EvenTwoRank.elementary F := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,he⟩ := hg ha
    rw [←he]
    simpa [MulAut.conj_apply,mul_assoc] using hb
  have he := eq_elementary_of_le hc hn B hB hBE
  refine ⟨g,le_antisymm hg ?_⟩
  rintro _ ⟨b,hb,rfl⟩
  rw [←he] at hb
  obtain ⟨a,ha,rfl⟩ := hb
  simpa [MulAut.conj_apply,mul_assoc] using ha
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ActorRecognition
