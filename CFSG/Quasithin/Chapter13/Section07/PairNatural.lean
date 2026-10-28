module

public import CFSG.Quasithin.Chapter13.Section07.PairCoreFactors
public import CFSG.Quasithin.Chapter13.Section07.PairLayers
public import CFSG.Quasithin.ChapterG.Section02.Binary.Module

/-!
# The actual natural section of the source pair

The proved internal conjugator carries the entire first span to the second.
This allows the binary G.2 quotient theorem to act on the original pair:
its quotient is elementary and is an equivariant tensor of natural S₃
modules. The coordinates remain the literal quotient map, and the two
original core intersections are complementary fixed and displacement spaces.

The final consumer constructs the source conjugator and combines the core
product, natural section and central intersection layer. It takes only
original F.9 applicability, the earlier abelian seed span and the contrary
nonabelian full span. No module, internal conjugator, quotient recognition,
or factor-normality conclusion is an input.
Source: Aschbacher–Smith, 13.7.10(2)–(3), printed pp.941–942.
-/

@[expose] public section

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise TensorProduct
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)

/-- The actual elementary section with its marked natural tensor and displacement spaces. -/
def PairNaturalSection (I S E A W Y:Subgroup G) : Prop :=
    ∃ hN:(E.subgroupOf S).Normal, letI:=hN;
    ∃ hEA:IsElementaryAbelian 2 (S⧸E.subgroupOf S), letI:=hEA;
    ∃ (e:(I⧸pCore 2 I)≃*S₃)
      (σ:Representation (ZMod 2) S₃ (Additive (S⧸E.subgroupOf S)))
      (c:Representation.BinaryConjugationSection I S E
        (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))))),
      (∀s:S,(c.coordinates s).toAdd=Additive.ofMul (QuotientGroup.mk' (E.subgroupOf S) s)) ∧
      Finite (multiplicitySpace σ) ∧
      IsCompl (c.imageSpace W) (c.imageSpace Y) ∧
      (∃ j:multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
          Additive (S⧸E.subgroupOf S),
        ∀a z,j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
          (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z)=σ a (j z)) ∧
      ∀u:I,(u:G)∈A→(u:G)∉W→
        LinearMap.ker (σ (e (QuotientGroup.mk' (pCore 2 I) u)) - (1 : Module.End (ZMod 2) (Additive (S⧸E.subgroupOf S)))) =c.imageSpace W ∧
        LinearMap.range (σ (e (QuotientGroup.mk' (pCore 2 I) u)) - (1 : Module.End (ZMod 2) (Additive (S⧸E.subgroupOf S)))) =c.imageSpace W ∧
        (c.imageSpace Y).map (σ (e (QuotientGroup.mk' (pCore 2 I) u)) - (1 : Module.End (ZMod 2) (Additive (S⧸E.subgroupOf S)))) =c.imageSpace W

include d

/-- The original pair quotient is the marked sum of natural modules. -/
theorem pair_natural_quotient
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hout : ¬ conjugate V₁ (g:G) ≤ Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let I:=A⊔B
    let S:=I.pCoreIn 2
    let E:=A⊓B
    let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    PairNaturalSection I S E A (A⊓Q) (B⊓Q) := by
  dsimp only
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let S:=I.pCoreIn 2
  let E:=A⊓B
  let Q:=X.pCoreIn 2
  let D:ChapterG.Section02.Setup G:=⟨V,V₁,L,T,H⟩
  have hAX:A≤X:=(VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hBX:B≤X := by
    rintro _ ⟨a,ha,rfl⟩
    change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact mul_mem (mul_mem (X.inv_mem g.property) (hAX ha)) g.property
  have hIX:I≤X:=sup_le hAX hBX
  have hpoint:V₁≤V:=h.point_lt.le.trans h.plus_le
  have hp:IsPGroup 2 A:=(pCore_isPGroup.map H.subtype).to_le (VH_le_core d h hU)
  have hIV:I≤normalizer (V:Set G):=hIX.trans d.normalizes_V
  obtain ⟨hVE,hES,hEN,_,_⟩:=D.rank_one_intersection_layer (g:G) hp
    (frattini_VH_le_point d h hU) hpoint hIV (d.normalizes_V g.property)
    (chosen_points_disjoint h (g:G) hout)
  change V≤E at hVE
  change E≤S at hES
  have hEI:E≤I:=inf_le_left.trans le_sup_left
  have hnE:I≤normalizer (E:Set G):=(normal_subgroupOf_iff_le_normalizer hEI).mp hEN
  have hQT:Q≤(T:Subgroup G):=h.sylow_centralizer.symm.le.trans inf_le_left
  obtain ⟨hcore,⟨e⟩⟩:=pair_twoCore_quotient d h hU hV g hout
  change S=I⊓Q at hcore
  have hnorm:S≤normalizer (A:Set G):=
    hcore.le.trans (inf_le_right.trans (hQT.trans (h.T_le_H.trans (le_normalizer_conjugateSpanBy V H))))
  obtain ⟨x,hx⟩:=pair_internal_conjugator d h hU hV g hout
  let k:G:=(x:G)⁻¹
  have hB:ChapterG.Section02.Setup.conjugate D.U k=B := by
    change A.map (MulAut.conj ((x:G)⁻¹)⁻¹).toMonoidHom=B
    rw [inv_inv]
    exact hx.symm
  have hDI:D.I k=I:=congrArg (A⊔·) hB
  have hDS:D.S k=S:=congrArg (fun J:Subgroup G=>J.pCoreIn 2) hDI
  have hDE:D.S₂ k=E:=congrArg (A⊓·) hB
  have hW:D.W k=A⊓Q := by
    change A⊓D.S k=A⊓Q
    rw [hDS,hcore,←inf_assoc,inf_eq_left.mpr (show A≤I from le_sup_left)]
  have hk:k∈D.I k:=hDI.symm ▸ I.inv_mem x.property
  have hkin:k∈normalizer (V:Set G):=hIV (I.inv_mem x.property)
  have eD:(D.I k⧸pCore 2 (D.I k))≃*S₃:=by rw [hDI];exact e
  have hnormD:D.S k≤normalizer (D.U:Set G):=hDS.symm ▸ hnorm
  have hind:(D.W k).relIndex D.U=2:=by
    rw [hW]
    change (A⊓Q).relIndex A=2
    rw [inf_relIndex_left]
    exact (nonabelian_core_indices d h hU hV).1
  have hVED:D.V≤D.S₂ k:=hDE.symm ▸ hVE
  have hESD:D.S₂ k≤D.S k:=by rw [hDE,hDS];exact hES
  have hEND:D.I k≤normalizer (D.S₂ k:Set G):=by rw [hDI,hDE];exact hnE
  have hsplit:=D.binary_core_factorization k hk eD hnormD hind
  let hND:((D.S₂ k).subgroupOf (D.S k)).Normal:=normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 (D.I k)).trans hEND)
  let hEAD:=D.binary_quotient_elementary k hk hkin hpoint hVED hESD hEND hnormD hsplit
    (fun _ hu=>square_VH_mem_point d h hU hu)
  have hh:=D.binary_natural_quotient k hk hkin hpoint hVED hESD hEND eD hnormD hind
    (commutator_VH_le_point d h hU) (fun _ hu=>square_VH_mem_point d h hU hu)
  have hconj:ChapterG.Section02.Setup.conjugate (D.W k) k=B⊓Q := by
    change (D.U⊓D.S k).map (MulAut.conj k⁻¹).toMonoidHom=B⊓Q
    rw [map_inf _ _ _ (MulAut.conj k⁻¹).injective]
    have hnS:I≤normalizer (S:Set G):=I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have heS:(D.S k).map (MulAut.conj k⁻¹).toMonoidHom=S:=by
      rw [hDS]
      exact mem_normalizer_iff_map_conj_eq.mp (hnS (by simpa only [k,inv_inv] using x.property))
    change ChapterG.Section02.Setup.conjugate D.U k⊓(D.S k).map (MulAut.conj k⁻¹).toMonoidHom=B⊓Q
    rw [hB,heS,hcore,←inf_assoc,inf_eq_left.mpr (show B≤I from le_sup_right)]
  generalize hπ:D.binaryCoreProjection k eD=π at hh
  have hπ':π=eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I k))):=
    hπ.symm.trans (D.binaryCoreProjection_eq k eD)
  clear hπ
  subst π
  have hall:PairNaturalSection (D.I k) (D.S k) (D.S₂ k) D.U (D.W k)
      (ChapterG.Section02.Setup.conjugate (D.W k) k) :=
    ⟨hND,hEAD,eD,hh⟩
  rw [hDI,hDS,hDE,hconj,hW] at hall
  exact hall
/-- The original 13.7.10(2)–(3), with a constructed g and literal factor,
quotient, action and central-layer markings. -/
theorem exists_source_pair_natural
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃ g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G))
        (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let A:=Section08.Source.VH H V
      let B:=conjugate A (g:G)
      let I:=A⊔B
      let S:=I.pCoreIn 2
      let E:=A⊓B
      let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      S=(A⊓Q)⊔(B⊓Q) ∧
      (S:Set G)=(A⊓Q:Set G)*(B⊓Q:Set G) ∧
      PairNaturalSection I S E A (A⊓Q) (B⊓Q) ∧
      ⁅E,I⁆≤V₁⊔conjugate V₁ (g:G) := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,
    pair_twoCore_factorization d h hU hV (inclusion le_sup_left g) hout,
    pair_twoCore_product d h hU hV (inclusion le_sup_left g) hout,
    pair_natural_quotient d h hU hV (inclusion le_sup_left g) hout,
    chosen_intersection_central_layer d h hU (inclusion le_sup_left g) hs⟩

end CFSG.Quasithin.Chapter13.Section07
