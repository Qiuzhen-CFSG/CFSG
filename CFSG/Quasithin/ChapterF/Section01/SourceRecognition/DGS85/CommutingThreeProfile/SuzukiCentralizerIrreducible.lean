module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralizerNaturalFactors
public import Theory.Representation.SL2.NaturalPairExtension
public import Theory.SpecificGroups.Suzuki.SylowSquares

/-!
# Irreducibility of the actual centralizer quotient

Write C = C_(Q_m)(G_m^(3)) and W = G_m^(2). If the literal C/W
were reducible, its two irreducible constituents would each have order
q². Reindexing along the actual covering actor of the natural Q_m/C
identifies both constituents as natural. The natural-pair extension
argument, the required instance of (5.17), then makes Q_m/W elementary.

But W lies in the neighboring two-core Q_y, and the original marked
Suzuki quotient maps Q_m onto its prescribed Sylow two-subgroup.
That Sylow subgroup has a nonidentity square. This contradicts elementary
abelianness, proving irreducibility with the original endpoint conjugation
formula and literal denominator. The comparison of the two field
presentations uses their common covering kernel, not an assumed alignment.

All earlier natural-center, reciprocal-commutator, critical-pair and
quotient-marking inputs remain explicit. This closes the nonbinary
irreducibility step, while source selection, binary alternatives and
final Chapter 12/13.1 premise discharge remain separate obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (12.9), printed pp.189--190; (5.17), printed p.117.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem source_suzuki_neighbor_excludes_elementary
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (N : Subgroup (G₀ L S))
    (hNy : N ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    [(N.subgroupOf (Q (reducedFamily L S) (base (reducedFamily L S) i))).Normal] :
    ¬ IsElementaryAbelian 2
      (Q (reducedFamily L S) (base (reducedFamily L S) i) ⧸
        N.subgroupOf (Q (reducedFamily L S) (base (reducedFamily L S) i))) := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S (!i)
  let Qm := Q F m
  let Qy := Q F y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer (!i))) (inclusion_injective _)
  let f : A →* SuzukiMatrixGroup n := eSuz.toMonoidHom.comp
    ((originalQuotient h (!i)).symm.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))
  have hf : Function.Surjective f :=
    eSuz.surjective.comp ((originalQuotient h (!i)).symm.surjective.comp
      (QuotientGroup.mk'_surjective _))
  have hk : f.ker = Qy.subgroupOf A := by
    have hk' : f.ker = pCore 2 A := by
      ext a
      change eSuz ((originalQuotient h (!i)).symm (QuotientGroup.mk' (pCore 2 A) a)) = 1 ↔ a ∈ pCore 2 A
      rw [map_eq_one_iff _ eSuz.injective, map_eq_one_iff _ (originalQuotient h (!i)).symm.injective]
      exact QuotientGroup.eq_one_iff a
    rw [hk']
    change pCore 2 A = (Q (reducedFamily L S) (base (reducedFamily L S) (!i))).subgroupOf A
    rw [←star_core h (!i)]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hQA : Qm ≤ A := (le_sup_left.trans hRy.ge).trans (map_subtype_le _)
  have hYA : Qy ≤ A := (le_sup_right.trans hRy.ge).trans (map_subtype_le _)
  have hR : (Ry : Subgroup A) = Qm.subgroupOf A ⊔ Qy.subgroupOf A := by
    have hh := congrArg (Subgroup.comap A.subtype) hRy
    rw [comap_map_eq_self_of_injective A.subtype_injective] at hh
    exact hh.trans (subgroupOf_sup hQA hYA)
  let P := Ry.mapSurjective hf
  have him : (P : Subgroup (SuzukiMatrixGroup n)) = (Qm.subgroupOf A).map f := by
    change (Ry : Subgroup A).map f = _
    rw [hR,Subgroup.map_sup,←hk,((Subgroup.map_eq_bot_iff _).mpr le_rfl),sup_bot_eq]
  intro hel
  have hs (q : Qm) : (q : G₀ L S)^2 ∈ N := by
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p
      (QuotientGroup.mk' (N.subgroupOf Qm) q)
    rw [←map_pow] at hh
    exact (QuotientGroup.eq_one_iff (N := N.subgroupOf Qm) (q^2)).mp hh
  obtain ⟨z,hz⟩ := suzukiSylow_exists_nontrivial_square hn (MulEquiv.refl _) P
  have hzm : (z : SuzukiMatrixGroup n) ∈ (Qm.subgroupOf A).map f := him ▸ z.property
  obtain ⟨q,hq,hqz⟩ := hzm
  apply hz
  apply Subtype.ext
  change (z : SuzukiMatrixGroup n)^2 = 1
  rw [←hqz,←map_pow]
  apply (show q^2 ∈ f.ker ↔ f (q^2) = 1 from Iff.rfl).mp
  rw [hk]
  exact hNy (hs ⟨q,hq⟩)

/-- The actual third-kernel centralizer modulo the full second kernel is irreducible. -/
theorem source_suzuki_centralizer_irreducible
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let A := star L S i
    let C := Q F m ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
    let W := conjugateSpanBy (V F (base F (!i)) 1 ⊓ Q F x) (stabilizer F m)
    ∃ hAC : A ≤ normalizer (C : Set (G₀ L S)),
    ∃ hW : (W.subgroupOf C).Normal,
      letI := hW
      let E := C ⧸ W.subgroupOf C
      Nat.card k ^ 3 ≤ Nat.card E ∧
      Nat.card E ≤ Nat.card k ^ (4 : ℕ) ∧
      ∃ hCE : IsElementaryAbelian 2 E,
        letI := hCE
        ∃ ρ : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) →*
          MulAut E,
          (∀ t : A, ∀ c : C,
            ρ ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) (QuotientGroup.mk' (W.subgroupOf C) c) =
              QuotientGroup.mk' (W.subgroupOf C) ⟨(t : G₀ L S)*c*(t : G₀ L S)⁻¹,
                (mem_normalizer_iff.mp (hAC t.property) c).mp c.property⟩) ∧
          let τ : Representation (ZMod 2) SL(2,k) (Additive E) :=
            FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
          τ.IsIrreducible := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S i
  let Qm := Q F m
  let C := Qm ⊓ centralizer (ballKernel F m 3 : Set (G₀ L S))
  let W := conjugateSpanBy (V F y 1 ⊓ Q F x) (stabilizer F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective (inclusion
    (show C ≤ stabilizer F m from inf_le_left.trans (Q_le_stabilizer F m))) (inclusion_injective _)
  obtain ⟨hAC,hW,hlo,hup,hCE,ρ,hρ,hfactors⟩ := source_suzuki_centralizer_two_factors
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  let _ := hW
  let _ := hCE
  let E := Additive (C ⧸ W.subgroupOf C)
  let τ := FrattiniAction.ofAutomorphismHom (ρ.comp e.symm.toMonoidHom)
  have hlarge : 1 < Nat.card E := lt_of_lt_of_le
    (Nat.one_lt_pow (by decide : 3 ≠ 0) Finite.one_lt_card) hlo
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hlarge
  let : Nontrivial (Subrepresentation τ) := ⟨⟨⊥,⊤,fun he =>
    (bot_ne_top : (⊥ : Submodule (ZMod 2) E) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule he)⟩⟩
  refine ⟨hAC,hW,hlo,hup,hCE,ρ,hρ,?_⟩
  dsimp only
  change τ.IsIrreducible
  apply IsSimpleOrder.of_forall_eq_top
  intro U hUb
  by_contra hUt
  obtain ⟨hcu,hcq,hi,hq⟩ := hfactors U hUb hUt
  let _ := hi
  let _ := hq
  change Nat.card (E ⧸ U.toSubmodule) = Nat.card k ^ (2 : ℕ) at hcq
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hQA : Qm ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hspan := source_linear_second_kernel_span h i hb hxadj hne T hT e hcommy.le hnear
  have hWC : W ≤ C := hspan.2.1.trans
    (source_suzuki_centralizer_second_kernel h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch).2.1
  have hAW : A ≤ normalizer (W : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans hspan.2.2.2.1
  let : (W.subgroupOf Qm).Normal := normal_subgroupOf_of_le_normalizer (hQA.trans hAW)
  let π₀ : A →* SL(2,k) := e.toMonoidHom.comp
    ((originalQuotient h i).symm.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))
  have hπ₀ : Function.Surjective π₀ := e.surjective.comp
    ((originalQuotient h i).symm.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk₀ : π₀.ker = Qm.subgroupOf A := by
    have hk' : π₀.ker = pCore 2 A := by
      ext a
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) a)) = 1 ↔ a ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff a
    rw [hk']
    change pCore 2 A = (Q (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf A
    rw [←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  let f : C →* Multiplicative E := {
    toFun c := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (W.subgroupOf C) c))
    map_one' := (QuotientGroup.mk' (W.subgroupOf C)).map_one
    map_mul' c d := (QuotientGroup.mk' (W.subgroupOf C)).map_mul c d }
  let cE : BinaryConjugationSection A C W (τ.comp π₀) := {
    section_le := inf_le_left.trans hQA
    kernel_le := hWC
    normalized := hAC
    coordinates := f
    onto := QuotientGroup.mk'_surjective (W.subgroupOf C)
    kernel_eq := QuotientGroup.ker_mk' (W.subgroupOf C)
    equivariant t c := by
      apply Additive.toMul.injective
      change QuotientGroup.mk' (W.subgroupOf C) _ =
        ρ (e.symm (π₀ t)) (QuotientGroup.mk' (W.subgroupOf C) c)
      have he : e.symm (π₀ t) =
          (originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t) := e.symm_apply_apply _
      rw [he,hρ] }
  obtain ⟨_,κ,_,_,hκAlg,π,hπ,hk,hκ,dQ,_⟩ := source_suzuki_centralizer_natural
    h i hb3 hxadj hne T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch
  have hdQA := dQ.section_le
  have hdCQ := dQ.kernel_le
  have hdN := dQ.normalized
  let fQ : Qm →* Multiplicative (Fin 2 → κ) := dQ.coordinates
  have hfs : Function.Surjective fQ := dQ.onto
  have hfk : fQ.ker = C.subgroupOf Qm := dQ.kernel_eq
  have hfe : ∀ t : A, ∀ q : Qm,
      (fQ ⟨(t : G₀ L S)*q*(t : G₀ L S)⁻¹,
        (mem_normalizer_iff.mp (hdN t.property) q).mp q.property⟩).toAdd =
        Matrix.mulVec (π t).val (fQ q).toAdd := dQ.equivariant
  let : CharP κ 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) κ).injective 2
  let : Algebra (ZMod 2) κ := ZMod.algebra κ 2
  let cQ : BinaryConjugationSection A Qm C
      ((Representation.SL2.BinarySmall.natural (K := κ)).comp π) := {
    section_le := hdQA
    kernel_le := hdCQ
    normalized := hdN
    coordinates := fQ
    onto := hfs
    kernel_eq := hfk
    equivariant t q := hfe t q }
  have hbig : 2 < Nat.card κ := by
    rw [hκ,hfield]
    change 2^1 < 2^(2*n+1)
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨a₀,ha0,ha1⟩ : ∃ a₀ : κ, a₀ ≠ 0 ∧ a₀ ≠ 1 := by
    by_contra! hh
    let f : Bool → κ := fun b => if b then 1 else 0
    have hs : Function.Surjective f := by
      intro a₀
      by_cases he : a₀ = 0
      · exact ⟨false,he.symm⟩
      · exact ⟨true,(hh a₀ he).symm⟩
    have hh := Nat.card_le_card_of_surjective f hs
    norm_num at hh
    omega
  have hcomm : ⁅Qm,C⁆ ≤ W := by
    rw [commutator_comm]
    exact (source_suzuki_centralizer_span_frattini h i hb3 hxadj hne T R hT hR e hz
      hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.1
  have helem := Representation.SL2.natural_pair_extension_elementary_of_small_factors
    A Qm C W inf_le_left hQA π hπ hk π₀ hπ₀ hk₀ τ cE cQ U
    (show Odd (2*n+1) from ⟨n,rfl⟩) (by omega) (hκ.trans hfield)
    (hcu.trans (by rw [hκ])) (hcq.trans (by rw [hκ])) a₀ ha0 ha1 hcomm
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hWy : W ≤ Q F y := CommutingTrivial.two_subgroup_le_Q F y (reduced_kernel_sylow h y)
    ((isPGroup_pCoreIn 2 _).to_le (hWC.trans inf_le_left))
    (hspan.2.1.trans (ballKernel_succ_le F hadj 1))
  exact source_suzuki_neighbor_excludes_elementary h i hn eSuz Ry hRy W hWy helem

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
