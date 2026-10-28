module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.ModelKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation.QuotientFaithfulness

/-!
# Transport of the two local quotient kernels

Both proper local residuals are aligned with the point and line locals
under the same K/O₂(K) projection and the same Sylow subgroup. A source
commutator in an intrinsic local two-core maps into the two-core of that
literal image. ModelKernel then shows that a cubic in both local kernels
centralizes the entire quotient. The original flag normalizer supplies
the rank bound that makes the Cartan action on this quotient faithful.

The final theorem says that the actual first cubic cannot centralize the
other residual section. TerminalOrientationSource applies it to the exact
G₂ reselected flag. Source: Aschbacher--Smith 11.1.2, printed pp.762--764.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public noncomputable section
variable {G M : Type*} [Group G] [Finite G] [Group M]

omit [Finite G] in
private theorem local_kernel_transport {K B : Subgroup G} (hBK : B ≤ K)
    (r : K →* M) (α : MulAut M) (x : normalizer (K : Set G))
    (hx : (x : G) ∈ Closure.coreQuotientCentralizer B)
    (hcompat : ∀ k : K, α (r k) = r (K.normalizerMonoidHom x k)) :
    ∀ y ∈ (B.subgroupOf K).map r,
      α y * y⁻¹ ∈ ((B.subgroupOf K).map r).pCoreIn 2 := by
  let D := (B.subgroupOf K).map r
  let p : B →* D := {
    toFun := fun b => ⟨r ⟨b,hBK b.property⟩,⟨⟨b,hBK b.property⟩,b.property,rfl⟩⟩
    map_one' := Subtype.ext (map_one r)
    map_mul' := by
      intro b c
      apply Subtype.ext
      exact map_mul r (⟨b,hBK b.property⟩ : K) (⟨c,hBK c.property⟩ : K) }
  have hp : Function.Surjective p := by
    rintro ⟨_,k,hk,rfl⟩
    exact ⟨⟨k,hk⟩,rfl⟩
  have hcore : (pCore 2 B).map p ≤ pCore 2 D := by
    let : ((pCore 2 B).map p).Normal := Subgroup.Normal.map inferInstance p hp
    exact le_sSup ⟨inferInstance,pCore_isPGroup.map p⟩
  intro y hy
  obtain ⟨b,hb⟩ := hp ⟨y,hy⟩
  have hb' : (p b : M) = y := congrArg Subtype.val hb
  rw [←hb']
  obtain ⟨c,hc,he⟩ := Closure.coreQuotientCentralizer_commutator hx b.property
  refine ⟨p c,hcore (mem_map_of_mem p hc),?_⟩
  change r ⟨c,hBK c.property⟩ = α (r ⟨b,hBK b.property⟩) * (r ⟨b,hBK b.property⟩)⁻¹
  have he' : (⟨c,hBK c.property⟩ : K) =
      K.normalizerMonoidHom x ⟨b,hBK b.property⟩ * (⟨b,hBK b.property⟩ : K)⁻¹ :=
    Subtype.ext he
  rw [he',map_mul,map_inv,hcompat]

/-- The same cubic cannot be in both proper local section kernels of a
PSL₃(4) component without being in the kernel on the entire component.
Both locals are aligned at the original Sylow and must be distinct. -/
theorem cubic_joint_local_kernel (T : Sylow 2 G) {K B C : Subgroup G}
    (hK : (⊤ : Subgroup K).IsCComponent)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hB : B ∈ localCComponents T) (hBK : B < K)
    (hC : C ∈ localCComponents T) (hCK : C < K) (hBC : B ≠ C)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (x : normalizer (K : Set G)) (hx3 : (x : G)^3 = 1)
    (hxB : (x : G) ∈ Closure.coreQuotientCentralizer B)
    (hxC : (x : G) ∈ Closure.coreQuotientCentralizer C) :
    (x : G) ∈ Closure.coreQuotientCentralizer K := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card F = 2^2 by simpa using hF)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) (P.mapSurjective hq)
    (unipotentSylow F (by decide : 0 < 2) (by simpa using hF))
  let a := MulAut.conj g
  let r := a.toMonoidHom.comp q
  have hr : Function.Surjective r := a.surjective.comp hq
  have hrker : r.ker = pCore 2 K := by
    ext k
    change a (e (QuotientGroup.mk' (pCore 2 K) k)) = 1 ↔ _
    rw [a.map_eq_one_iff,e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff k
  let : Group.IsNilpotent r.ker := by rw [hrker]; exact pCore_isNilpotent
  have hrP : (P : Subgroup K).map r = unipotent F := by
    rw [←Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  have hkP : r.ker ≤ (P : Subgroup K) := by
    rw [hrker]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hBP : B.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
    hP.symm ▸ ChapterA.Section03.SourceEmbeddings.local_restrict hB hBK.le
  have hCP : C.subgroupOf K ∈ localCComponents (P : Subgroup K) :=
    hP.symm ▸ ChapterA.Section03.SourceEmbeddings.local_restrict hC hCK.le
  obtain ⟨b,hb⟩ := local_eq_rootLift hF r hr P hrP hkP hK hBP
    (fun he => hBK.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨c,hc⟩ := local_eq_rootLift hF r hr P hrP hkP hK hCP
    (fun he => hCK.not_ge (subgroupOf_eq_top.mp he))
  have hbc : b ≠ c := by
    intro he
    apply hBC
    have hh := congrArg (map K.subtype) (hb.trans ((congrArg (rootLift r) he).trans hc.symm))
    simpa only [map_subgroupOf_eq_of_le hBK.le,map_subgroupOf_eq_of_le hCK.le] using hh
  let E := e.trans a
  let ψ := (MulAut.congr E).toMonoidHom.comp (Closure.coreQuotientAction K)
  let α := ψ x
  have hα3 : α^3 = 1 := by
    change (ψ x)^3 = 1
    rw [←map_pow,show x^3 = 1 from Subtype.ext hx3,map_one]
  have hcompat (k : K) : α (r k) = r (K.normalizerMonoidHom x k) := by
    change E (Closure.coreQuotientAction K x (E.symm (E (QuotientGroup.mk' (pCore 2 K) k)))) = _
    rw [E.symm_apply_apply,Closure.coreQuotientAction_apply_mk]
    rfl
  have hpb := local_kernel_transport hBK.le r α x hxB hcompat
  have hpc := local_kernel_transport hCK.le r α x hxC hcompat
  rw [hb,rootLift_map hF r hr] at hpb
  rw [hc,rootLift_map hF r hr] at hpc
  have hα : α = 1 := by
    apply ModelKernel.cubic_eq_one_of_local_kernels hF α hα3
    · cases b <;> cases c
      · exact (hbc rfl).elim
      · simpa only [rootLocal_true] using hpc
      · simpa only [rootLocal_true] using hpb
      · exact (hbc rfl).elim
    · cases b <;> cases c
      · exact (hbc rfl).elim
      · simpa only [rootLocal_false] using hpb
      · simpa only [rootLocal_false] using hpc
      · exact (hbc rfl).elim
  have hact : Closure.coreQuotientAction K x = 1 :=
    (MulAut.congr E).injective (hα.trans (map_one _).symm)
  exact ⟨x,MonoidHom.mem_ker.mpr hact,rfl⟩

open CFSG.Quasithin.Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- In the original PGL triangle, a nontrivial cubic in the first local
kernel cannot lie in the other local kernel. The same actor and full
intrinsic quotient are retained throughout the comparison. -/
theorem first_projective_cubic_not_in_other_kernel (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hd : S.field.degree = 2) {K K₀ X E : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hne₀ : K₀ ≠ f.Li 0)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hEX : E ≤ X) (hE : Nat.card E = 3)
    (hEB : E ≤ Closure.coreQuotientCentralizer (f.Li 0)) :
    ¬ E ≤ Closure.coreQuotientCentralizer K₀ := by
  intro hEC
  apply first_projective_cubic_not_central D S f hu hd hX hK hk hEX hE
  have hn : normalizer (f.Vi 0 : Set G) ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2
  have ht : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  intro x hx
  let e := c.cartanTorusEquiv hX
  have hc : Nat.card S.field.Carrierˣ = 3 := by rw [Nat.card_units,S.field.card_eq,hd]; decide
  have hcube (a : S.field.Carrierˣ) : a^3 = 1 := by rw [←hc]; exact pow_card_eq_one'
  have hx3 : (⟨x,hEX hx⟩ : X)^3 = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    exact Prod.ext (hcube _) (hcube _)
  exact cubic_joint_local_kernel T ht ((f.invariant 0).trans hn)
    (flag_mem_local_of_model D S f 0 hm₁).1 hLK hK₀.1 hK₀K hne₀.symm hk
    ⟨x,hn (f.cartan_normalizes hu hX 0 (hEX hx))⟩ (congrArg Subtype.val hx3)
    (hEB hx) (hEC hx)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
