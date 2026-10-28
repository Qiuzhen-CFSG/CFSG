module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialConjugacy.MathieuInvolutions.Tables
public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradPointwiseStabilizer

/-!
# The literal pointwise tetrad stabilizer

Each row of the finite table preserves the six binary hexacode generators.
Its coordinate permutation is faithful, so the existing order-60 theorem
proves exhaustion of the linear factor. The systematic hexacode encoder
then parametrizes the sixteen translations vanishing on the first tetrad.
The resulting 960 permutations are connected to the actual pointwise
stabilizer through its existing affine equivalence.

All encoders and stabilizer equivalences are the attributed ATLAS ports;
no abstract Mathieu recognition is used.
-/

@[expose] public section
open Atlas.Codes
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.MathieuInvolutions

def permutation (k : Fin 60) : Equiv.Perm HexIndex :=
  hexIndexEquiv.trans ((Equiv.mk (forward k) (backward k) (left_inv k) (right_inv k)).trans hexIndexEquiv.symm)
def localMap (k : Fin 6) : KIsometry := ![1,localU,localV,localW,localKappa,localKappa⁻¹] k
def raw (k : Fin 60) : Monomial HexIndex :=
  ⟨permutation k, fun i => localMap (letters k (hexIndexEquiv i))⟩
theorem preserves_basis : ∀ k i, Monomial.act (raw k) (hexGenerators i) ∈ hexacode := by
  intro k i
  rw [hexacode_systematic]
  revert k i
  decide
def automorphism (k : Fin 60) : HexAutomorphisms :=
  ⟨raw k, monomial_mem_of_hexBasis _ (preserves_basis k)⟩
theorem fixed : ∀ k, (raw k).perm (0,0) = (0,0) := by intro k; fin_cases k <;> decide
theorem local_fixed : ∀ k u, (raw k).localMap (0,0) u = u := by intro k; fin_cases k <;> decide
def element (k : Fin 60) : hexPointKernel (0,0) :=
  ⟨⟨automorphism k, fixed k⟩, LinearEquiv.ext (local_fixed k)⟩
theorem element_injective : Function.Injective element := by
  intro i j h
  apply forward_injective i j
  intro k
  have hh := congrArg (fun a : hexPointKernel (0,0) => hexIndexEquiv (a.val.val.val.perm (hexPos k))) h
  change hexIndexEquiv (hexIndexEquiv.symm (forward i (hexIndexEquiv (hexPos k)))) =
    hexIndexEquiv (hexIndexEquiv.symm (forward j (hexIndexEquiv (hexPos k)))) at hh
  simpa only [index_hexPos, Equiv.apply_symm_apply] using hh
theorem element_surjective : Function.Surjective element := by
  apply ((Nat.bijective_iff_injective_and_card element).mpr ⟨element_injective, ?_⟩).2
  rw [hexPointKernel_card]
  simp


def zeroWord (u v : Fin 4) : hexZeroCoordinate (0,0) :=
  ⟨⟨systematicEncoder ![0,rowLabel u,rowLabel v], systematic_mem _⟩, rfl⟩

noncomputable def stabilizerElement (a : Index) : TetradPointStabilizer (0,0) :=
  tetradPointStabilizerEquiv (0,0) ⟨Multiplicative.ofAdd (zeroWord a.1 a.2.1),element a.2.2⟩

noncomputable def model (a : Index) : Mathieu24CodeModel := (stabilizerElement a).val

theorem zeroWord_surjective (x : hexZeroCoordinate (0,0)) :
    ∃ u v, zeroWord u v = x := by
  refine ⟨rowLabel.symm (x.val.val (hexPos 1)),rowLabel.symm (x.val.val (hexPos 2)),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change systematicEncoder _ = x.val.val
  have he : ![0,rowLabel (rowLabel.symm (x.val.val (hexPos 1))),
      rowLabel (rowLabel.symm (x.val.val (hexPos 2)))] = hexProjection firstThree x.val := by
    funext i
    fin_cases i
    · exact x.prop.symm
    · exact rowLabel.apply_symm_apply _
    · exact rowLabel.apply_symm_apply _
  rw [he]
  exact systematic_reconstruct x.val

theorem stabilizerElement_surjective : Function.Surjective stabilizerElement := by
  intro s
  obtain ⟨x,rfl⟩ := (tetradPointStabilizerEquiv (0,0)).surjective s
  obtain ⟨u,v,huv⟩ := zeroWord_surjective x.left.toAdd
  obtain ⟨j,hj⟩ := element_surjective x.right
  refine ⟨(u,v,j),congrArg (tetradPointStabilizerEquiv (0,0)) ?_⟩
  exact SemidirectProduct.ext (congrArg Multiplicative.ofAdd huv) hj

def pointEquiv : Omega ≃ Point := Equiv.prodCongr hexIndexEquiv (Equiv.refl (Fin 4))

theorem rowLabel_add : ∀ u v : K,
    rowLabel.symm (u+v) = rowLabel.symm u ^^^ rowLabel.symm v := by decide

theorem localRows_spec : ∀ l k,
    rowLabel.symm (localMap l (rowLabel k)) = localRows l k := by decide

theorem translationRows_spec : ∀ u v i,
    rowLabel.symm ((zeroWord u v).val.val i) = translationRows u v (hexIndexEquiv i) := by
  intro u
  fin_cases u <;> decide

theorem model_coordinates (a : Index) (x : Omega) :
    pointEquiv ((model a).val x) = act a (pointEquiv x) := by
  obtain ⟨i,k⟩ := x
  change (hexIndexEquiv ((raw a.2.2).perm i),
    rowLabel.symm ((raw a.2.2).localMap ((raw a.2.2).perm i) (rowLabel k) +
      (zeroWord a.1 a.2.1).val.val ((raw a.2.2).perm i))) = _
  rw [rowLabel_add, translationRows_spec]
  change (hexIndexEquiv (hexIndexEquiv.symm (forward a.2.2 (hexIndexEquiv i))),
    rowLabel.symm (localMap (letters a.2.2
      (hexIndexEquiv (hexIndexEquiv.symm (forward a.2.2 (hexIndexEquiv i))))) (rowLabel k)) ^^^
    translationRows a.1 a.2.1 (hexIndexEquiv (hexIndexEquiv.symm (forward a.2.2 (hexIndexEquiv i))))) = _
  rw [hexIndexEquiv.apply_symm_apply, localRows_spec]
  rfl


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.MathieuInvolutions
