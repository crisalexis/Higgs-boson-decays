
import numpy as np
import matplotlib.pyplot as plt
import scienceplots

plt.style.use(["science", "ieee", "no-latex"])

# ==========================================
# 1. IMPORTAR ARRAYS DE MATHEMATICA
# ==========================================

lo = np.loadtxt(
    "GammaLO_Muon_keV.csv",
    delimiter=",",
    skiprows=1
)

virtual = np.loadtxt(
    "DeltaGammaVirtual_Muon_keV.csv",
    delimiter=",",
    skiprows=1
)

real = np.loadtxt(
    "GammaReal_Muon_keV.csv",
    delimiter=",",
    skiprows=1
)

# ==========================================
# 2. EXTRAER MASAS Y ANCHOS
# ==========================================

mH = lo[:, 0]

GammaLO = lo[:, 1]
DeltaGammaVirtual = virtual[:, 1]
GammaReal = real[:, 1]

# Comprobar que las masas coincidan
assert np.allclose(mH, virtual[:, 0], rtol=0, atol=1e-8)
assert np.allclose(mH, real[:, 0], rtol=0, atol=1e-8)

# ==========================================
# 3. CALCULAR EL ANCHO NLO
# ==========================================

GammaNLO = GammaLO + DeltaGammaVirtual + GammaReal

CorreccionNLO = 100 * (GammaNLO / GammaLO - 1)

# Exportar lista NLO como array
np.savetxt(
    "GammaNLO_Muon_keV.csv",
    np.column_stack((mH, GammaNLO)),
    delimiter=",",
    header="mH_GeV,GammaNLO_keV",
    comments=""
)

# ==========================================
# 4. PLOT: GAMMA LO VS GAMMA NLO
# ==========================================

fig, ax = plt.subplots(figsize=(5, 3.5))

ax.plot(mH, GammaLO, "--", label="LO")
ax.plot(mH, GammaNLO, "-", label="NLO")

ax.set_xlabel(r"$m_H$ [GeV]")
ax.set_ylabel(r"$\Gamma(H\to\mu^+\mu^-)$ [keV]")

ax.set_xlim(95, 150)
ax.legend()
ax.grid(alpha=0.2)

fig.tight_layout()
fig.savefig("Hmumu_LO_vs_NLO.pdf")
plt.show()

# ==========================================
# 5. PLOT: CONTRIBUCIONES INDIVIDUALES
# ==========================================

fig, ax = plt.subplots(figsize=(5, 3.5))

ax.plot(mH, GammaLO,
        label=r"$\Gamma_{\mathrm{LO}}$")

ax.plot(mH, DeltaGammaVirtual,
        label=r"$\Delta\Gamma_{\mathrm{virtual}}$")

ax.plot(mH, GammaReal,
        label=r"$\Gamma_{\mathrm{real}}$")

ax.plot(mH, GammaNLO, "k--",
        label=r"$\Gamma_{\mathrm{NLO}}$")

ax.set_xlabel(r"$m_H$ [GeV]")
ax.set_ylabel(r"$\Gamma$ [keV]")
ax.set_xlim(95, 150)

ax.legend()
ax.grid(alpha=0.2)

fig.tight_layout()
fig.savefig("Hmumu_Contribuciones.pdf")
plt.show()

# ==========================================
# 6. PLOT: CORRECCION PORCENTUAL
# ==========================================

fig, ax = plt.subplots(figsize=(5, 3.5))

ax.plot(mH, CorreccionNLO)

ax.axhline(0, color="gray", linestyle=":")

ax.set_xlabel(r"$m_H$ [GeV]")
ax.set_ylabel(
    r"$(\Gamma_{\mathrm{NLO}}/"
    r"\Gamma_{\mathrm{LO}}-1)\times100$ [%]"
)

ax.set_xlim(95, 150)
ax.grid(alpha=0.2)

fig.tight_layout()
fig.savefig("Hmumu_Correccion_Porcentual.pdf")
plt.show()

# ==========================================
# 7. RESULTADO MAS CERCANO A 125 GeV
# ==========================================

i = np.argmin(np.abs(mH - 125))

print(f"mH = {mH[i]:.8f} GeV")
print(f"Gamma LO       = {GammaLO[i]:.8f} keV")
print(f"Delta virtual  = {DeltaGammaVirtual[i]:.8f} keV")
print(f"Gamma real     = {GammaReal[i]:.8f} keV")
print(f"Gamma NLO      = {GammaNLO[i]:.8f} keV")
print(f"Correccion NLO = {CorreccionNLO[i]:.5f} %")
