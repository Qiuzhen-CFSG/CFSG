module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalModuleNormal
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalDecomposition
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.SymmetricFiveThree
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.OddFactorDisjoint
public import Theory.Representation.NormalElementaryQuotient.NormalMoved
public import Theory.GroupTheory.Commutator.FixedSeedKernel
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.Commutator.FixedSeedMovement

/-!
# The marked terminal S₅ × S₃ module decomposition

The actual conjugation action of Y/O₂(Y) on U satisfies the complete adequate
B.5 classifier. The marked product excludes every other alternative and orders
the source factors by the original quotient coordinates. The odd image A₃ of L₂
lifts disjointness from U/C_U(Y) to U itself. Normality of both residual images
then gives crossed fixedness. Since T fixes Z and U=⟨Z^Y⟩, the original seed
commutators generate the entire two moved summands.

Thus [U,Y]=[U,K]⊕[U,L₂]=[Z,K]⊕[Z,L₂], with all subgroups in the original G.
`false_of_module_analysis` applies these conclusions to the existing terminal
endpoint. ProductAnalysis remains an earlier input whose construction belongs
to the preceding source argument. No decomposition or extra classifier premise is used.
ComponentAnalysis is needed upstream to construct the product data, not here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.6(3)
and the completion of 12.3.1, printed pp.105 and 812.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

private theorem K_le_Y : P.K ≤ P.Y := le_sup_left.trans le_sup_left
private theorem L2_le_Y : P.L2 ≤ P.Y := le_sup_right.trans le_sup_left

/-- The source classification factors match the two full symmetric coordinates. -/
theorem moduleAction_marked_twoFactors (A : P.ProductAnalysis) :
    ∃ d : SourceTwoFactorCase (P.moduleAction A),
      d.first.map A.quotient.toMonoidHom = (⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥ ∧
      d.second.map A.quotient.toMonoidHom = (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤ :=
  SymmetricFiveThree.marked_twoFactors A.quotient (P.moduleAction A)
    (P.moduleAction_alternative A)

private theorem commutator_map (X : Subgroup G) (hX : X ≤ P.Y) :
    (⁅P.U.subgroupOf P.Y,X.subgroupOf P.Y⁆).map P.Y.subtype = ⁅P.U,X⁆ := by
  rw [map_commutator,map_subgroupOf_eq_of_le P.U_le_Y,map_subgroupOf_eq_of_le hX]

/-- Quotient disjointness lifts to actual U because the second residual image is odd. -/
theorem module_moved_disjoint (A : P.ProductAnalysis) :
    Disjoint ⁅P.U,P.K⁆ ⁅P.U,P.L2⁆ := by
  obtain ⟨d,hd1,hd2⟩ := P.moduleAction_marked_twoFactors A
  let q := QuotientGroup.mk' (pCore 2 P.Y)
  let B := (P.K.subgroupOf P.Y).map q
  let C := (P.L2.subgroupOf P.Y).map q
  have hb : B ≤ d.first := by
    apply (map_le_map_iff_of_injective (f := A.quotient.toMonoidHom) A.quotient.injective).mp
    rw [hd1,map_map]
    change (P.K.subgroupOf P.Y).map (A.quotient.toMonoidHom.comp q) ≤ _
    rw [A.first_image]
    exact prod_mono le_top le_rfl
  have hc : C ≤ d.second := by
    apply (map_le_map_iff_of_injective (f := A.quotient.toMonoidHom) A.quotient.injective).mp
    rw [hd2,map_map]
    change (P.L2.subgroupOf P.Y).map (A.quotient.toMonoidHom.comp q) ≤ _
    rw [A.second_image]
    exact prod_mono le_rfl le_top
  have hd := d.disjoint_moved_of_odd B C hb hc (P.moduleAction_second_odd A)
  have hd' : Disjoint
      (NormalElementaryQuotient.commutatorSpace (P.U.subgroupOf P.Y) (P.K.subgroupOf P.Y))
      (NormalElementaryQuotient.commutatorSpace (P.U.subgroupOf P.Y) (P.L2.subgroupOf P.Y)) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (P.U.subgroupOf P.Y) q
      (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
        (P.module_centralizer_eq A).symm),
      NormalElementaryQuotient.commutatorSpace_eq (P.U.subgroupOf P.Y) q
      (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
        (P.module_centralizer_eq A).symm)]
    exact hd
  have hi : Disjoint ⁅P.U.subgroupOf P.Y,P.K.subgroupOf P.Y⁆
      ⁅P.U.subgroupOf P.Y,P.L2.subgroupOf P.Y⁆ := by
    apply Subgroup.disjoint_def.mpr
    intro y hy1 hy2
    let v : Additive (P.U.subgroupOf P.Y) :=
      Additive.ofMul ⟨y,(commutator_le_left _ _) hy1⟩
    have hz : v = 0 := Submodule.disjoint_def.mp hd' v hy1 hy2
    exact congrArg (fun x : Additive (P.U.subgroupOf P.Y) => (x.toMul : P.Y)) hz
  rw [←P.commutator_map P.K P.K_le_Y,←P.commutator_map P.L2 P.L2_le_Y]
  apply Subgroup.disjoint_def.mpr
  rintro x ⟨a,ha,rfl⟩ ⟨b,hb,he⟩
  have hab : b = a := P.Y.subtype_injective he
  subst b
  exact congrArg Subtype.val (Subgroup.disjoint_def.mp hi ha hb)

/-- The first residual fixes the whole second moved summand, not merely its quotient. -/
theorem module_crossed_fixed (A : P.ProductAnalysis) :
    P.K ≤ centralizer (⁅P.U,P.L2⁆ : Subgroup G) := by
  have hWU : ⁅P.U,P.L2⁆ ≤ P.U := le_normalizer_iff_commutator_le_left.mp
    (P.L2_le_Y.trans (le_normalizer_componentOrbit P.Z P.Y))
  have hc : ⁅⁅P.U,P.L2⁆,P.K⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply (le_inf (commutator_mono hWU le_rfl)
      (le_normalizer_iff_commutator_le_left.mp (P.K_le_Y.trans (P.module_second_normalized A)))).trans
    exact (P.module_moved_disjoint A).le_bot
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)

private theorem module_eq_seed (A : P.ProductAnalysis) (X B : Subgroup G)
    (hX : X ≤ P.Y) (hB : B ≤ P.Y)
    (hn : ((B.subgroupOf P.Y).map
      (A.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y)))).Normal)
    (hgenerates : X ⊔ B ⊔ (T : Subgroup G) = P.Y)
    (hcross : X ≤ centralizer (⁅P.U,B⁆ : Subgroup G)) : ⁅P.U,B⁆ = ⁅P.Z,B⁆ := by
  let q := QuotientGroup.mk' (pCore 2 P.Y)
  let U₀ := P.U.subgroupOf P.Y
  let Z₀ := P.Z.subgroupOf P.Y
  let K₀ := X.subgroupOf P.Y
  let B₀ := B.subgroupOf P.Y
  let T₀ := (T : Subgroup G).subgroupOf P.Y
  have hn' : ((B₀.map q).map A.quotient.toMonoidHom).Normal := by
    rw [map_map]
    change ((B.subgroupOf P.Y).map
      (A.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.Y)))).Normal
    exact hn
  let : (B₀.map q).Normal := hn'.of_map_injective A.quotient.injective
  have hZU : Z₀ ≤ U₀ := fun _ hz => le_componentOrbit P.Z P.Y hz
  have hspan : U₀ = conjugateSpanBy Z₀ ⊤ := by
    apply map_injective P.Y.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le P.U_le_Y,
      map_subgroupOf_eq_of_le P.Z_le_Y,←MonoidHom.range_eq_map,range_subtype]
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer P.Z P.Y _
        (le_conjugateSpanBy P.Z P.Y) (le_normalizer_conjugateSpanBy P.Z P.Y)
    · exact conjugateSpanBy_le (le_componentOrbit P.Z P.Y)
        (le_normalizer_componentOrbit P.Z P.Y)
  have hgen : K₀ ⊔ B₀ ⊔ T₀ = ⊤ := by
    apply map_injective P.Y.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hX,
      map_subgroupOf_eq_of_le hB,map_subgroupOf_eq_of_le P.sylow_le_Y,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hgenerates
  have hTZ : T₀ ≤ centralizer (Z₀ : Set P.Y) := by
    intro t ht z hz
    exact Subtype.ext (((mem_omegaCenterIn_iff _ _).mp hz).2.1 t ht).symm
  have hKW : K₀ ≤ centralizer ((⁅U₀,B₀⁆ : Subgroup P.Y) : Set P.Y) := by
    intro k hk x hx
    apply Subtype.ext
    apply hcross hk x
    rw [←P.commutator_map B hB]
    exact mem_map_of_mem P.Y.subtype hx
  have he := conjugateSpan_commutator_eq_seed Z₀ U₀ K₀ B₀ T₀ q
    (show q.ker ≤ centralizer (U₀ : Set P.Y) from
      ((QuotientGroup.ker_mk' _).trans (P.module_centralizer_eq A).symm).le)
    hZU hspan hgen hTZ hKW
  have hm := congrArg (map P.Y.subtype) he
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le P.U_le_Y,
    map_subgroupOf_eq_of_le P.Z_le_Y,map_subgroupOf_eq_of_le hB] at hm
  exact hm

/-- The full moved second summand is the original omega-center seed summand. -/
theorem module_second_eq_seed (A : P.ProductAnalysis) : ⁅P.U,P.L2⁆ = ⁅P.Z,P.L2⁆ := by
  apply P.module_eq_seed A P.K P.L2 P.K_le_Y P.L2_le_Y
  · rw [A.second_image]
    infer_instance
  · rfl
  · exact P.module_crossed_fixed A

/-- The first moved summand is normalized by the same original local group. -/
theorem module_first_normalized (A : P.ProductAnalysis) :
    P.Y ≤ normalizer (⁅P.U,P.K⁆ : Subgroup G) := by
  apply P.module_moved_normalized A P.K P.K_le_Y
  rw [A.first_image]
  infer_instance

/-- The second residual fixes the first moved summand. -/
theorem module_crossed_fixed_first (A : P.ProductAnalysis) :
    P.L2 ≤ centralizer (⁅P.U,P.K⁆ : Subgroup G) := by
  have hWU : ⁅P.U,P.K⁆ ≤ P.U := le_normalizer_iff_commutator_le_left.mp
    (P.K_le_Y.trans (le_normalizer_componentOrbit P.Z P.Y))
  have hc : ⁅⁅P.U,P.K⁆,P.L2⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply (le_inf (commutator_mono hWU le_rfl)
      (le_normalizer_iff_commutator_le_left.mp (P.L2_le_Y.trans (P.module_first_normalized A)))).trans
    exact (P.module_moved_disjoint A).symm.le_bot
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)

/-- The full first moved summand is likewise the original seed summand. -/
theorem module_first_eq_seed (A : P.ProductAnalysis) : ⁅P.U,P.K⁆ = ⁅P.Z,P.K⁆ := by
  apply P.module_eq_seed A P.L2 P.K P.L2_le_Y P.K_le_Y
  · rw [A.first_image]
    infer_instance
  · rw [sup_comm P.L2 P.K]
    rfl
  · exact P.module_crossed_fixed_first A

/-- The source moved group is the join of the two literal residual commutators. -/
theorem module_moved_eq_sup (A : P.ProductAnalysis) :
    ⁅P.U,P.Y⁆ = ⁅P.U,P.K⁆ ⊔ ⁅P.U,P.L2⁆ := by
  let W := ⁅P.U,P.K⁆ ⊔ ⁅P.U,P.L2⁆
  have hnorm : P.Y ≤ normalizer (W : Set G) :=
    (le_inf (P.module_first_normalized A) (P.module_second_normalized A)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hspan : P.U = conjugateSpanBy P.Z P.Y := by
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer P.Z P.Y _
        (le_conjugateSpanBy P.Z P.Y) (le_normalizer_conjugateSpanBy P.Z P.Y)
    · exact conjugateSpanBy_le (le_componentOrbit P.Z P.Y)
        (le_normalizer_componentOrbit P.Z P.Y)
  apply le_antisymm
  · conv_lhs => rw [hspan]
    apply conjugateSpan_commutator_le_of_fixed_generators P.Z P.Y P.K P.L2
      (T : Subgroup G) W P.Z_le_Y rfl hnorm
    · exact (commutator_mono (le_componentOrbit P.Z P.Y) le_rfl).trans le_sup_left
    · exact (commutator_mono (le_componentOrbit P.Z P.Y) le_rfl).trans le_sup_right
    · intro t ht z hz
      exact (((mem_omegaCenterIn_iff _ _).mp hz).2.1 t ht).symm
  · exact sup_le (commutator_mono le_rfl P.K_le_Y) (commutator_mono le_rfl P.L2_le_Y)

/-- The literal two-factor direct sum asserted on p.812, with both seed identities. -/
theorem module_decomposition (A : P.ProductAnalysis) :
    ⁅P.U,P.Y⁆ = ⁅P.U,P.K⁆ ⊔ ⁅P.U,P.L2⁆ ∧
    Disjoint ⁅P.U,P.K⁆ ⁅P.U,P.L2⁆ ∧
    ⁅P.U,P.K⁆ = ⁅P.Z,P.K⁆ ∧ ⁅P.U,P.L2⁆ = ⁅P.Z,P.L2⁆ :=
  ⟨P.module_moved_eq_sup A,P.module_moved_disjoint A,
    P.module_first_eq_seed A,P.module_second_eq_seed A⟩

/-- The literal conditional source application at the end of 12.3.1.
ProductAnalysis remains an earlier source obligation with the product owner. -/
theorem false_of_module_analysis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (A : P.ProductAnalysis) : False :=
  P.false_of_module_decomposition structural A (P.module_moved_disjoint A)
    (P.K_le_Y.trans (P.module_second_normalized A)) (P.module_second_eq_seed A)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
