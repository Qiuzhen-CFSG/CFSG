module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.AbelianClosure
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.G2BinaryPointElementaryAction
public import Theory.ElementaryAbelian.Quotient

/-!
# The smaller original F.9 closure in the unitary natural action

F.9 supplies Φ(U_H)≤V₁. Since V₁ acts trivially on V, the literal image of
U_H in its actual automizer is elementary. The marked T image lies in the
original unipotent group, and L₁T covers the derived point parabolic. The
native normal-elementary calculation therefore puts that image in ABC,
which fixes V₃. The conjugate-span criterion proves U_H elementary.

The parameters are the original F.9 setup and its genuine natural-six
marking: no elementary-closure or classifier conclusion is a premise.
The original 13.3.2 marking and 13.3.18(1) applicability are separate earlier
source producers; the assembly retains their discharge.

Source: Aschbacher–Smith, Lemma 13.3.18, printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

omit [Finite G] in
private theorem image_normalizes {N L A : Subgroup G} {K : Type*} [Group K]
    (f:N→*K) (h: L≤normalizer (A:Set G)) :
    (L.subgroupOf N).map f≤normalizer ((A.subgroupOf N).map f:Set K) := by
  apply le_trans (map_mono (show L.subgroupOf N≤normalizer (A.subgroupOf N:Set N) from ?_))
    ((A.subgroupOf N).le_normalizer_map f)
  intro l hl
  apply mem_normalizer_iff.mpr
  intro a
  exact mem_normalizer_iff.mp (h hl) a.val

/-- The elementary image of the smaller original closure requires no
abelianness assumption on that closure. -/
theorem seed_closure_model_image_elementary (h:D.Hypothesis) :
    ∀rho:Automizer D.V→*Atlas.G2.Model F,
    IsElementaryAbelian 2 ((inducedAutomizer D.V D.UH).map rho) := by
  intro rho
  let N := normalizer (D.V:Set G)
  let f : N→*Atlas.G2.Model F := rho.comp D.V.normalizerMonoidHom.rangeRestrict
  have hUN : D.UH≤N := h.UH_le_QH.trans (h.QH_le_T.trans h.T_normalizes_V)
  let j : D.UH→*N := inclusion hUN
  let q : D.UH→*Atlas.G2.Model F := f.comp j
  have hphi : frattini D.UH≤q.ker := by
    intro u hu
    have huZ : (u:G)∈D.V₁ := h.frattini_UH_le_point ⟨u,hu,rfl⟩
    have huC : (u:G)∈centralizer (D.V:Set G) :=
      ((le_centralizer_iff.mp h.H_centralizes).trans
        (centralizer_le h.V_le_H)) huZ
    have he : D.V.normalizerMonoidHom (j u)=1 :=
      show j u∈D.V.normalizerMonoidHom.ker from by
        rw [normalizerMonoidHom_ker]
        exact huC
    have her : D.V.normalizerMonoidHom.rangeRestrict (j u)=1 := Subtype.ext he
    change rho (D.V.normalizerMonoidHom.rangeRestrict (j u))=1
    rw [her,map_one]
  let _ : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
  let _ : IsElementaryAbelian 2 (D.UH ⧸ frattini D.UH) :=
    isElementaryAbelian_quotient_frattini
  let qb := QuotientGroup.lift (frattini D.UH) q hphi
  have heq : qb.range=q.range := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini D.UH) y
      exact ⟨y,rfl⟩
    · rintro ⟨y,rfl⟩
      exact ⟨QuotientGroup.mk' (frattini D.UH) y,rfl⟩
  have hqe : IsElementaryAbelian 2 q.range := heq ▸
    IsElementaryAbelian.of_surjective qb.rangeRestrict qb.rangeRestrict_surjective
  have hqrange : q.range=((inducedAutomizer D.V D.UH).map rho) := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨D.V.normalizerMonoidHom.rangeRestrict (j y),⟨j y,y.prop,rfl⟩,rfl⟩
    · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
      exact ⟨⟨y.val,hy⟩,rfl⟩
  exact hqrange ▸ hqe

/-- The actual F.9 smaller closure is elementary under its original marked
natural-six action. The normal-elementary image step is proved above. -/
theorem seed_closure_elementary_of_point_action (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    (∀v:Additive D.V, E v∈seed ↔ (v.toMul:G)∈D.Vplus) →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    IsElementaryAbelian 2 D.UH := by
  let :=h.elementary
  dsimp only
  intro rho E he hs hT hP
  let A := (inducedAutomizer D.V D.UH).map rho
  let :IsElementaryAbelian 2 A := seed_closure_model_image_elementary h rho
  have hA : A≤Atlas.G2.unipotent :=
    (map_mono (map_mono (comap_mono (h.UH_le_QH.trans h.QH_le_T)))).trans hT
  have hn : Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤normalizer (A:Set _) := by
    apply hP.trans
    change (((D.L₁⊔(D.T:Subgroup G)).subgroupOf (normalizer (D.V:Set G))).map
      D.V.normalizerMonoidHom.rangeRestrict).map rho ≤ normalizer (A:Set (Atlas.G2.Model F))
    rw [map_map]
    simpa only [A,inducedAutomizer,map_map,ChapterF.Section09.Setup.UH] using
      image_normalizes (rho.comp D.V.normalizerMonoidHom.rangeRestrict)
        (h.local_le.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
  apply seed_closure_elementary h
  intro u hu v hv
  let n : normalizer (D.V:Set G) :=
    ⟨u,(h.UH_le_QH.trans (h.QH_le_T.trans h.T_normalizes_V)) hu⟩
  let a : Automizer D.V := D.V.normalizerMonoidHom.rangeRestrict n
  let w : Additive D.V := Additive.ofMul ⟨v,h.plus_le hv⟩
  have ha : rho a∈A := ⟨a,⟨n,hu,rfl⟩,rfl⟩
  have hw : E w∈seed := (hs w).mpr hv
  have hf := Atlas.G2.Natural.BinaryPointFlag.elementary_normalized_point_fixes_seed
    A hA hn (rho a) ha (E w) hw
  rw [←he] at hf
  have heq := E.injective hf
  have hc : u*v*u⁻¹=v := congrArg (fun x:Additive D.V => (x.toMul:G)) heq
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
