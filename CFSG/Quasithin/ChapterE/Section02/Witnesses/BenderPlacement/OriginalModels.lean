module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.LinearTwo
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.Suzuki
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Witness

/-!
# Original pairs with their Bender field degrees and quotient models

The original E.2.4 pair, its literal normal-core quotient, and its field
degree are stored together. Linear and Suzuki alternatives retain the exact
image of the original maximal intersection under the same model equivalence.
The dihedral alternative has degree one. A separate model mark retains the
ambient Bender exponent, including 2m+1 for the concrete Suzuki carrier.
The existing core-free model constructions supply these original quotient
records without any new classification or recognition assumption.

Source: Aschbacher–Smith E.2.4 and E.2.7–9, printed pp.217–222.
-/

public section
noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
inductive ModelAt (D : Type*) [Group D] : ℕ → Prop
  | linear {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSL D 2 (2^n)) : ModelAt D n
  | unitary {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSU D 3 (2^n)) : ModelAt D n
  | suzuki {m : ℕ} (hm : 0 < m) (model : Nonempty (D ≃* SuzukiMatrixGroup m)) : ModelAt D (2*m+1)

inductive QuotientModel {I : Type*} [Group I] (A : Subgroup I) (d : ℕ) : Type _
  | dihedral (degree_eq : d=1) (p a : ℕ) (prime : p.Prime) (odd : p ≠ 2) (positive : 0<a)
      (equiv : (I ⧸ A.normalCore) ≃* DihedralGroup (p^a))
  | linear (degree_gt_one : 1<d) (equiv : (I ⧸ A.normalCore) ≃* SL(2,GaloisField 2 d))
      (borel : (A.map (QuotientGroup.mk' A.normalCore)).map equiv.toMonoidHom =
        SpecialLinearGroup.rankOneBorel (GaloisField 2 d))
  | suzuki (m : ℕ) (positive : 0<m) (degree_eq : d=2*m+1)
      (equiv : (I ⧸ A.normalCore) ≃* SuzukiMatrixGroup m)
      (borel : ∃c:SuzukiMatrixGroup m,
        (A.map (QuotientGroup.mk' A.normalCore)).map equiv.toMonoidHom =
          (SuzukiBorelSubgroup m).map (MulAut.conj c).toMonoidHom)

structure OriginalWitness {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H) (M V : Subgroup H) (n : ℕ) where
  pair : QuotientLift.Pair T M V
  degree : ℕ
  positive : 0<degree
  degree_dvd : degree ∣ n
  model : QuotientModel (M.subgroupOf pair.subgroup) degree

variable {H : Type*} [Group H] [Finite H]

noncomputable def OriginalWitness.of_dihedral {T : Sylow 2 H} {M V : Subgroup H} {n : ℕ}
    (w : Solvable.Witness T M V) : OriginalWitness T M V n := Classical.choice (by
  classical
  let pair : QuotientLift.Pair T M V :=
    ⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,w.sylow_eq,w.core_two_closed⟩
  obtain ⟨p,a,hp,hp2,ha,⟨e⟩⟩ := w.dihedral
  exact ⟨⟨pair,1,by decide,one_dvd _,.dihedral rfl p a hp hp2 ha e⟩⟩)

@[expose] noncomputable def coreFreeQuotientEquiv {I : Type*} [Group I]
    (A : Subgroup I) (hA : A.normalCore = ⊥) : (I ⧸ A.normalCore) ≃* I :=
  (QuotientGroup.quotientMulEquivOfEq hA).trans QuotientGroup.quotientBot

theorem coreFreeQuotientEquiv_mk {I : Type*} [Group I]
    (A : Subgroup I) (hA : A.normalCore = ⊥) (x : I) :
    coreFreeQuotientEquiv A hA (QuotientGroup.mk' A.normalCore x) = x := rfl

theorem coreFreeQuotientEquiv_map {I : Type*} [Group I]
    (A : Subgroup I) (hA : A.normalCore = ⊥) (B : Subgroup I) :
    (B.map (QuotientGroup.mk' A.normalCore)).map (coreFreeQuotientEquiv A hA).toMonoidHom = B := by
  rw [Subgroup.map_map]
  have he : (coreFreeQuotientEquiv A hA).toMonoidHom.comp (QuotientGroup.mk' A.normalCore) =
      MonoidHom.id I := by ext x; rfl
  rw [he,Subgroup.map_id]

noncomputable def OriginalWitness.of_linear {T : Sylow 2 H} {M V : Subgroup H} {n : ℕ}
    (w : LinearTwo.Witness T M V n) : OriginalWitness T M V n := by
  let A := M.subgroupOf w.pair.subgroup
  let e := (coreFreeQuotientEquiv A w.corefree).trans w.model
  have hb : (A.map (QuotientGroup.mk' A.normalCore)).map e.toMonoidHom =
      SpecialLinearGroup.rankOneBorel (GaloisField 2 w.degree) := by
    change (A.map (QuotientGroup.mk' A.normalCore)).map
      (w.model.toMonoidHom.comp (coreFreeQuotientEquiv A w.corefree).toMonoidHom) = _
    rw [←Subgroup.map_map,coreFreeQuotientEquiv_map]
    exact w.borel_model
  exact ⟨w.pair,w.degree,by have := w.degree_gt_one; omega,w.degree_dvd,.linear w.degree_gt_one e hb⟩

noncomputable def OriginalWitness.of_suzuki {T : Sylow 2 H} {M V : Subgroup H} {m : ℕ}
    (w : SuzukiWitness T M V m) : OriginalWitness T M V (2*m+1) := by
  let A := M.subgroupOf w.pair.subgroup
  let e := (coreFreeQuotientEquiv A w.core_eq_bot).trans w.equiv
  have hb : ∃c:SuzukiMatrixGroup w.parameter,
      (A.map (QuotientGroup.mk' A.normalCore)).map e.toMonoidHom =
        (SuzukiBorelSubgroup w.parameter).map (MulAut.conj c).toMonoidHom := by
    change ∃c, (A.map (QuotientGroup.mk' A.normalCore)).map
      (w.equiv.toMonoidHom.comp (coreFreeQuotientEquiv A w.core_eq_bot).toMonoidHom) = _
    rw [←Subgroup.map_map,coreFreeQuotientEquiv_map]
    exact w.borel_conjugate
  exact ⟨w.pair,2*w.parameter+1,by omega,w.degree_dvd,.suzuki w.parameter w.positive rfl e hb⟩



end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
