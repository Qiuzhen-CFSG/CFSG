module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlaneQuotient
public import CFSG.Quasithin.Chapter3.Defs
public import Theory.GroupTheory.PCoreImage

/-!
# Local cores and minimal escape for a paired binary plane

Every paired-plane automizer is already induced by its original component
centralizer. For a normalizing overgroup J whose two-core centralizes W,
the symmetric-three image puts O₂(C_J(U)) in C_J(W). Relative normality
of that kernel then identifies O₂(C_J(U)) with O₂(J).

The source local base retains L₀ = O²(C_L(U)) and T₀ = C_T(U).
Failure of ambient containment selects an actual minimal escaping H over
this base, with U in O₂(H) and the inherited SQTK hypotheses. This does
not prove that H has characteristic two. The source equality
C_{LT}(U) = L₀T₀, its Sylow arrangement, and the constrained-group
argument remain with qt-d-1222-nonff-doubled.
The chosen-orbit application is NonFFSourceDoubledBinaryLocalCore.
Source: Aschbacher–Smith §7.7.2–3, printed pp.704–706, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore
open ChapterE BinaryLinearThree DoubledBinaryPlanes DoubledBinaryPlaneQuotient

/-- The original two-residual L₀, embedded in the ambient group. -/
@[expose] def localResidual {G : Type*} [_root_.Group G] (L U : Subgroup G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer (U : Set G) : Subgroup G)).map
    (L ⊓ centralizer (U : Set G)).subtype

/-- The original source product L₀T₀, written as a subgroup join. -/
@[expose] def localBase {G : Type*} [_root_.Group G] (L T U : Subgroup G) : Subgroup G :=
  localResidual L U ⊔ (T ⊓ centralizer (U : Set G))

/-- Finite minimal descent inside the actual centralizer supplies an SQTK
group with the original central two-subgroup in its two-core. -/
theorem minimal_escape
    {G : Type*} [_root_.Group G] [Finite G] {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (U B M : Subgroup G)
    (hp : IsPGroup 2 U) (hU : U ≠ ⊥) (hUB : U ≤ B)
    (hBC : B ≤ centralizer (U : Set G))
    (hout : ¬ centralizer (U : Set G) ≤ M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar B M ∧ H ≤ centralizer (U : Set G) ∧
      U ≤ H.pCoreIn 2 ∧ IsSQTK κ H := by
  classical
  let S : Set (Subgroup G) :=
    {H | B ≤ H ∧ H ≤ centralizer (U : Set G) ∧ ¬ H ≤ M}
  obtain ⟨H,hH⟩ := (Set.toFinite S).exists_minimalFor id S
    ⟨centralizer (U : Set G),hBC,le_rfl,hout⟩
  have hBH : B ≤ H := hH.1.1
  have hHC : H ≤ centralizer (U : Set G) := hH.1.2.1
  have hcore : U ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes hp (hUB.trans hBH)
    (hHC.trans (Subgroup.centralizer_le_normalizer _))
  have hne : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hU (le_bot_iff.mp (he ▸ hcore))
  have hHN : H ≤ normalizer (U : Set G) :=
    hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hs := (hG.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
    ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
  refine ⟨H,?_,hHC,hcore,(IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs⟩
  refine ⟨⟨⟨hne,hBH⟩,hH.1.2.2⟩,?_⟩
  intro Y hY hYH
  exact hH.2 ⟨hY.1.2,hYH.trans hHC,hY.2⟩ hYH

/-- The original component centralizer induces the entire paired-plane fixer. -/
theorem component_centralizer_image
    {G : Type*} [_root_.Group G] (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (ha : ∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (NaturalDual.action g (E w)))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W₀ b w)))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    inducedAutomizer W₀ (L ⊓ centralizer (ambientPlane W₀ E v f : Set G)) =
      inducedAutomizer W₀ (centralizer (ambientPlane W₀ E v f : Set G)) := by
  apply le_antisymm (map_mono (comap_mono inf_le_right))
  rintro b ⟨n,hn,rfl⟩
  obtain ⟨g,hg⟩ := doubledBinary_ambientPlane_fixer_inner W₀ E a hcov n v f hfv hn
  obtain ⟨l,hl⟩ := hq g
  have he : W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l) =
      W₀.normalizerMonoidHom.rangeRestrict n := by
    apply a.injective
    rw [ha,hl]
    exact hg
  have hc : (l : G) ∈ centralizer (ambientPlane W₀ E v f : Set G) := by
    intro x hx
    let w : W₀ := ⟨x,ambientPlane_le_orbit W₀ E v f hx⟩
    have hh := congrArg (fun b : Automizer W₀ => ((b.val w : W₀) : G)) he
    change (l : G) * x * (l : G)⁻¹ = (n : G) * x * (n : G)⁻¹ at hh
    have hc : x * (n : G) = (n : G) * x := hn x hx
    rw [← hc,mul_inv_cancel_right] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact ⟨inclusion hLN l,⟨l.property,hc⟩,he⟩

private theorem centralizer_core
    {G : Type*} [_root_.Group G] (W₀ J U : Subgroup G)
    (hJN : J ≤ normalizer (W₀ : Set G)) (hUW : U ≤ W₀)
    (hQ : J.pCoreIn 2 ≤ centralizer (W₀ : Set G))
    (himage : inducedAutomizer W₀ (J ⊓ centralizer (U : Set G)) =
      inducedAutomizer W₀ (centralizer (U : Set G)))
    (hp : pCore 2 (inducedAutomizer W₀ (centralizer (U : Set G))) = ⊥) :
    (J ⊓ centralizer (U : Set G)).pCoreIn 2 = J.pCoreIn 2 := by
  let K := J ⊓ centralizer (U : Set G)
  let C := J ⊓ centralizer (W₀ : Set G)
  let P := inducedAutomizer W₀ (centralizer (U : Set G))
  let i : K →* normalizer (W₀ : Set G) := inclusion (inf_le_left.trans hJN)
  let q := W₀.normalizerMonoidHom.rangeRestrict.comp i
  have hq (k : K) : q k ∈ P := ⟨i k,k.property.2,rfl⟩
  let π : K →* P := q.codRestrict P hq
  have hπ : Function.Surjective π := by
    intro b
    have hb := b.property
    change (b : Automizer W₀) ∈ inducedAutomizer W₀ (centralizer (U : Set G)) at hb
    rw [← himage] at hb
    obtain ⟨n,hn,he⟩ := hb
    exact ⟨⟨n,hn⟩,Subtype.ext he⟩
  have hm : (pCore 2 K).map π ≤ pCore 2 P :=
    le_sSup ⟨(inferInstance : (pCore 2 K).Normal).map π hπ,pCore_isPGroup.map π⟩
  have hk : K.pCoreIn 2 ≤ centralizer (W₀ : Set G) := by
    rintro x ⟨k,hk,rfl⟩
    have he : π k = 1 := by
      have hh := hm (mem_map_of_mem π hk)
      rw [show pCore 2 P = ⊥ from hp] at hh
      exact hh
    have he' : W₀.normalizerMonoidHom (i k) = 1 :=
      congrArg (fun b : P => b.val.val) he
    change i k ∈ W₀.normalizerMonoidHom.ker at he'
    rw [normalizerMonoidHom_ker] at he'
    exact he'
  have hCK : C ≤ K := inf_le_inf_left J (centralizer_le hUW)
  have hJC : J ≤ normalizer (C : Set G) :=
    (le_inf J.le_normalizer (hJN.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hKC : K.pCoreIn 2 ≤ C := le_inf ((pCoreIn_le 2 K).trans inf_le_left) hk
  apply le_antisymm
  · exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K) hKC
      (hCK.trans (K.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image K (pCore 2 K))))).trans
      (pCoreIn_mono_of_normalizes inf_le_left hJC)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J)
      (le_inf (pCoreIn_le 2 J) (hQ.trans (centralizer_le hUW)))
      (inf_le_left.trans (J.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))

/-- The paired-plane centralizer inside J has the same two-core as J.
The normal whole-orbit centralizer kernel need not be a two-group. -/
theorem pairedPlane_core
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ L J : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (hLJ : L ≤ J)
    (hJN : J ≤ normalizer (W₀ : Set G))
    (hQ : J.pCoreIn 2 ≤ centralizer (W₀ : Set G))
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) =
        NaturalDual.action (q l) (E w))
    (a : Automizer W₀ ≃* MulAut Group)
    (ha : ∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (NaturalDual.action g (E w)))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W₀ b w)))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    (J ⊓ centralizer (ambientPlane W₀ E v f : Set G)).pCoreIn 2 = J.pCoreIn 2 := by
  have hi := component_centralizer_image W₀ L hLN q hq E a ha hcov v f hfv
  apply centralizer_core W₀ J (ambientPlane W₀ E v f) hJN
    (ambientPlane_le_orbit W₀ E v f) hQ
  · apply le_antisymm (map_mono (comap_mono inf_le_right))
    exact hi.ge.trans (map_mono (comap_mono (inf_le_inf_right _ hLJ)))
  · exact twoCore_eq_bot_of_symmetricThree
      (ambientPlane_equiv W₀ L hLN q hq E hE a ha hcov v f hfv)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryLocalCore
