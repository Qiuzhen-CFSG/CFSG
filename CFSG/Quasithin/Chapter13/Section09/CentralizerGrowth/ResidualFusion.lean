module
public import CFSG.Quasithin.Chapter13.Section09.CentralizerGrowth.ResidualFusion.Coordinates

/-!
# The literal residual Sylow and involution fusion in 13.9.5

Apply the two-transfer dihedral-product theorem to the original Sylow of
C_G(t). The earlier orthogonal-normalizer action supplies exactly two inputs:
the ambient t-class on J(T) is the union of the two factor involution sets,
and the second factor T₂ lies in O²(C_G(t)). The marked coordinates derive
reflection fusion and transport the resulting Sylow back to this same T₂.
Sylow conjugacy in the residual then proves that every residual involution
lies in t's ambient class, the premise consumed by the terminal contradiction
in `CentralizerGrowth.Transfer`.

Both earlier inputs remain explicit here and belong to the normalizer-action
assembly of 13.9.5. No recognition of the residual as L₃(2) or A₆ is needed
for this conclusion, and no subgroup or Sylow marking is replaced.

Source: Aschbacher–Smith 13.9.5, printed p.971 (combined1March2004 manuscript).
-/


public noncomputable section
open Subgroup SymmetricFourWreath
namespace CFSG.Quasithin.Chapter13.Section09.Marking
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)

/-- The actual second dihedral factor is Sylow in the t-centralizer residual. -/
theorem residual_sylow_of_axis_fusion
    (haxes : ∀ x∈m.dihedralBase, orderOf x=2 →
      (IsConj m.t x ↔ x∈m.factorSylow 1 ∨ x∈m.factorSylow turn))
    (hsecond : m.factorSylow turn ≤
      (pResidual 2 (centralizer ({m.t}:Set G))).map (centralizer ({m.t}:Set G)).subtype) :
    ∃ Q : Sylow 2 ((pResidual 2 (centralizer ({m.t}:Set G))).map
      (centralizer ({m.t}:Set G)).subtype),
      (Q : Subgroup _).map ((pResidual 2 (centralizer ({m.t}:Set G))).map
        (centralizer ({m.t}:Set G)).subtype).subtype=m.factorSylow turn := by
  let C:=centralizer ({m.t}:Set G)
  let R:=pResidual 2 C
  let X:=R.map C.subtype
  obtain ⟨S,hS⟩ := m.thompson_sylow_t
  rw [m.elementary_thompson] at hS
  let e : S ≃* D8×D8 := m.baseProductSylowEquiv S hS
  have he (ab:D8×D8) : (((e.symm ab:S):C):G)=m.baseProductEmbedding ab := rfl
  have hc : (e.symm (DihedralGroup.r 2,1):C)∈center C := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    change (x:G) * (((e.symm (DihedralGroup.r 2,1):S):C):G) =
      (((e.symm (DihedralGroup.r 2,1):S):C):G) * (x:G)
    rw [he,m.baseProductEmbedding_axis]
    exact mem_centralizer_singleton_iff.mp x.property
  have ha (x:S) (hx:orderOf x=2) :
      IsConj (C.subtype (e.symm (DihedralGroup.r 2,1))) (C.subtype x) ↔
        (e x).1=1 ∨ (e x).2=1 := by
    have hxJ : ((x:C):G)∈m.dihedralBase := hS ▸ mem_map_of_mem C.subtype x.property
    have hxo : orderOf ((x:C):G)=2 :=
      (orderOf_coe (x:C)).trans ((orderOf_coe x).trans hx)
    have hh := haxes ((x:C):G) hxJ hxo
    have hxE : ((x:C):G)=m.baseProductEmbedding (e x) := by rw [←he];simp
    change IsConj (((e.symm (DihedralGroup.r 2,1):S):C):G) ((x:C):G) ↔ _
    rw [he,m.baseProductEmbedding_axis]
    rw [hxE,m.baseProductEmbedding_mem_first,m.baseProductEmbedding_mem_second] at hh
    rw [hxE]
    exact hh.trans or_comm
  have hb (b:D8) : (e.symm (1,b):C)∈R := by
    have hh := hsecond ((m.baseProductEmbedding_mem_second 1 b).mpr rfl)
    obtain ⟨r,hr,hrb⟩ := hh
    have hr' : r=(e.symm (1,b):C) := Subtype.ext hrb
    exact hr' ▸ hr
  obtain ⟨Q,hQ⟩ := DihedralProductTransfer.exists_residual_sylow S e hc
    (DihedralProductTransfer.reflection_fusion_of_axes C.subtype S e hc ha) hb
  let eR : R ≃* X := R.equivMapOfInjective C.subtype C.subtype_injective
  refine ⟨Q.mapSurjective (f:=eR.toMonoidHom) eR.surjective,?_⟩
  change ((Q:Subgroup R).map eR.toMonoidHom).map X.subtype=m.factorSylow turn
  have hm : X.subtype.comp eR.toMonoidHom=C.subtype.comp R.subtype := rfl
  rw [map_map,hm,←map_map,hQ]
  apply le_antisymm
  · rintro x ⟨_,⟨⟨a,b⟩,⟨ha,_⟩,rfl⟩,rfl⟩
    change m.baseProductEmbedding (a,b)∈m.factorSylow turn
    exact (m.baseProductEmbedding_mem_second a b).mpr ha
  · intro x hx
    have hxJ := m.factorSylow_le_dihedralBase turn hx
    rw [←m.range_baseProductEmbedding] at hxJ
    obtain ⟨⟨a,b⟩,rfl⟩ := hxJ
    have ha := (m.baseProductEmbedding_mem_second a b).mp hx
    exact ⟨(e.symm (a,b):C),⟨(a,b),⟨ha,mem_top _⟩,rfl⟩,rfl⟩

/-- Every involution in the literal t-centralizer residual belongs to t's
ambient conjugacy class; this is the residual premise of 13.9.5's contradiction. -/
theorem residual_involution_fusion_of_axes
    (haxes : ∀ x∈m.dihedralBase, orderOf x=2 →
      (IsConj m.t x ↔ x∈m.factorSylow 1 ∨ x∈m.factorSylow turn))
    (hsecond : m.factorSylow turn ≤
      (pResidual 2 (centralizer ({m.t}:Set G))).map (centralizer ({m.t}:Set G)).subtype)
    (x:G) (hx:x∈(pResidual 2 (centralizer ({m.t}:Set G))).map
      (centralizer ({m.t}:Set G)).subtype) (ho:orderOf x=2) : IsConj m.t x := by
  let X:Subgroup G:=(pResidual 2 (centralizer ({m.t}:Set G))).map
    (centralizer ({m.t}:Set G)).subtype
  obtain ⟨Q,hQ⟩ := m.residual_sylow_of_axis_fusion haxes hsecond
  let a:X:=⟨x,hx⟩
  have hao:orderOf a=2 := (orderOf_coe a).symm.trans ho
  have hp:IsPGroup 2 (zpowers a) := IsPGroup.of_card (n:=1) (by rw[Nat.card_zpowers,hao];rfl)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq X P Q
  have hb : MulAut.conj g a∈(Q:Subgroup X) := by
    rw[←hg]
    exact mem_map_of_mem _ (hP (mem_zpowers a))
  have hbc : IsConj x ((MulAut.conj g a:X):G) := by
    change IsConj (X.subtype a) (X.subtype (MulAut.conj g a))
    exact X.subtype.map_isConj (isConj_iff.mpr ⟨g,rfl⟩)
  have hb2 : ((MulAut.conj g a:X):G)∈m.factorSylow turn :=
    hQ ▸ mem_map_of_mem X.subtype hb
  have hbo : orderOf ((MulAut.conj g a:X):G)=2 := by
    rw[orderOf_coe, (MulAut.conj g).orderOf_eq,hao]
  have hc := (haxes _ (m.factorSylow_le_dihedralBase turn hb2) hbo).mpr (Or.inr hb2)
  exact hc.trans hbc.symm
end CFSG.Quasithin.Chapter13.Section09.Marking
