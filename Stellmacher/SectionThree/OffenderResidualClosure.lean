module
public import Stellmacher.SectionThree.NormalClosureResidualJoin
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionOne.OneSevenIdentification

/-!
# The residual product underlying the action offender closure

For a finite solvable group that is a Section Three P-set member relative
to its distinguished Sylow subgroup, a quotient action satisfying the
Section One hypotheses has offender closure E = O^2(quotient) J whenever
J is nontrivial. This is the barred E used in Stellmacher (6.4), Journal of
Algebra 190 (1997), p.31; the bars and the residual superscript are lost
in the repository's abbreviated LaTeX transcription.

The global identification in (1.7) makes J normal in the quotient Sylow.
Its lift cannot lie in the original 2-core, since that core maps into the
quotient's trivial 2-core. The Section Three normal-closure theorem applies
(3.4) to that lift, and residual functoriality identifies the resulting
image with the quotient residual. The given action is used throughout.
-/

namespace Stellmacher.SectionThree
universe u

public theorem offender_normalClosure_eq_residual_sup
    {G X V : Type u} [Group G] [Finite G] [Group X] [Finite X]
    [Group V] [Finite V] [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (S : Sylow 2 G) (h : Hypotheses G (S : Subgroup G))
    (hP : (⊤ : Subgroup G) ∈ PSet (⊤ : Subgroup G) (S : Subgroup G))
    (hsolv : Group.IsSolvable G) (q : G →* X) (hq : Function.Surjective q)
    (hOne : SectionOne.Hypotheses X V)
    (hJ : SectionOne.oneJ (V := V) ((S : Subgroup G).map q) ≠ ⊥) :
    SectionOne.oneE (V := V) ((S : Subgroup G).map q) =
      twoResidualAmbient (⊤ : Subgroup X) ⊔
        SectionOne.oneJ (V := V) ((S : Subgroup G).map q) := by
  classical
  let T := S.mapSurjective hq
  let J := SectionOne.oneJ (V := V) (T : Subgroup X)
  let P : Subgroup G := ⊤
  let f : P →* X := q.comp P.subtype
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := hq x
    exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
  have hSm : ((S : Subgroup G).subgroupOf P).map f = (T : Subgroup X) := by
    rw [show f = q.comp P.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le (show (S : Subgroup G) ≤ P from le_top)]
    rfl
  obtain ⟨hid, _⟩ := SectionOne.oneSeven_global_identification hOne T
  have hJN := (SectionOne.oneSeven_global_product hOne T).1
  have hJS : J ≤ (T : Subgroup X) := by
    change SectionOne.oneJ (V := V) (T : Subgroup X) ≤ _
    rw [hid]
    exact inf_le_left
  have hJn : (J.subgroupOf (T : Subgroup X)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs j hj
    change j ∈ SectionOne.oneJ (V := V) (T : Subgroup X) at hj
    change s * j * s⁻¹ ∈ SectionOne.oneJ (V := V) (T : Subgroup X)
    rw [hid] at hj ⊢
    exact ⟨T.mul_mem (T.mul_mem hs hj.1) (T.inv_mem hs), hJN.conj_mem j hj.2 s⟩
  have hcore : (twoCoreAmbient P).map q ≤ pCore 2 X := by
    change ((pCore 2 P).map P.subtype).map q ≤ _
    rw [Subgroup.map_map]
    let _ : ((pCore 2 P).map f).Normal := Subgroup.Normal.map inferInstance f hf
    exact le_sSup ⟨inferInstance, (pCore_isPGroup (p := 2) (G := P)).map f⟩
  have hnot : ¬ (S : Subgroup G) ⊓ (J.comap f).map P.subtype ≤ twoCoreAmbient P := by
    intro hc
    apply hJ
    apply bot_unique
    intro j hj
    have hjS := hJS hj
    obtain ⟨s, hs, hsj⟩ := Subgroup.mem_map.mp hjS
    have hsJ : (⟨s, Subgroup.mem_top s⟩ : P) ∈ J.comap f := by
      change q s ∈ J
      rwa [hsj]
    have hsC := hc ⟨hs, Subgroup.mem_map.mpr ⟨⟨s, Subgroup.mem_top s⟩, hsJ, rfl⟩⟩
    have hjC := hcore (Subgroup.mem_map.mpr ⟨s, hsC, hsj⟩)
    rwa [hOne.twoCore_eq_bot] at hjC
  let _ : Group.IsSolvable G := hsolv
  have heq := normalClosure_eq_residual_sup_of_normal_sylow_image
    (S : Subgroup G) h P hP inferInstance f hf J
    (hSm.symm ▸ hJS) (hSm.symm ▸ hJn) hnot
  have hR : ((twoResidualAmbient P).subgroupOf P).map f =
      twoResidualAmbient (⊤ : Subgroup X) := by
    rw [show f = q.comp P.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le (show twoResidualAmbient P ≤ P from le_top)]
    exact map_twoResidualAmbient_of_subgroup_image P q ⊤ (by
      rw [show P = ⊤ from rfl, ← MonoidHom.range_eq_map, q.range_eq_top_of_surjective hq])
  rw [hR] at heq
  exact heq

end Stellmacher.SectionThree
